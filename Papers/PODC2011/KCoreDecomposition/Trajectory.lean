import Papers.PODC2011.KCoreDecomposition.Basic

/-!
# The synchronous estimate trajectory

In the synchronous model of §4.2 every node, in every round, knows the latest estimates of all its
neighbours and recomputes `core ← computeIndex(est, u, core)` (see `Run.lean` for the
message-level semantics and the proof that it produces exactly this trajectory).

`traj G s u` is the estimate of `u` after `s` update steps: `traj G 0 = degree`.

* `coreness_le_traj` — safety (Theorem 2, synchronous version);
* `traj_succ_le` — estimates never increase;
* `traj_stab` / `traj_eq_coreness_of_le` — liveness (Theorem 3): after `stab G` steps the estimates
  are exactly the corenesses, and they never change afterwards;
* `stab_le_sum` — `stab G ≤ Σ (d(u) − k(u))` (the content of Theorem 4);
* `progress` — while some estimate is wrong, every step makes at least one more node correct
  (the key claim in the proof of Theorem 5);
* `stab_le_card_sub` — `stab G ≤ N − |{u : d(u) = k(u)}|` and `stab_le_card_sub_minDegree` —
  `stab G ≤ N − K` with `K` the number of minimum-degree nodes (Corollary 1).
-/

open Finset

set_option linter.unusedSectionVars false

namespace KCoreDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- View a vector of natural numbers as a vector of estimates in `ℕ∞`. -/
abbrev toE (c : V → ℕ) : V → ℕ∞ := fun v => (c v : ℕ∞)

/-- One synchronous update step: every node applies `computeIndex` to its neighbours' current
estimates, with its own current estimate as the cap. -/
noncomputable def step (c : V → ℕ) : V → ℕ := fun u => computeIndex G (toE c) u (c u)

/-- `traj G s` is the estimate vector after `s` synchronous update steps. -/
noncomputable def traj : ℕ → V → ℕ
  | 0 => fun u => G.degree u
  | s + 1 => step G (traj s)

variable {G}

@[simp] theorem traj_zero (u : V) : traj G 0 u = G.degree u := rfl

theorem traj_succ (s : ℕ) : traj G (s + 1) = step G (traj G s) := rfl

theorem traj_succ_apply (s : ℕ) (u : V) :
    traj G (s + 1) u = computeIndex G (toE (traj G s)) u (traj G s u) := rfl

theorem traj_succ_le (s : ℕ) (u : V) : traj G (s + 1) u ≤ traj G s u :=
  computeIndex_le _ _ _

theorem traj_anti (u : V) : Antitone fun s => traj G s u :=
  antitone_nat_of_succ_le fun s => traj_succ_le s u

theorem traj_le_degree (s : ℕ) (u : V) : traj G s u ≤ G.degree u :=
  (traj_anti u (Nat.zero_le s)).trans_eq rfl

/-- **Theorem 2 (Safety), synchronous version.** Every estimate is at least the coreness. -/
theorem coreness_le_traj : ∀ (s : ℕ) (u : V), coreness G u ≤ traj G s u
  | 0, u => coreness_le_degree u
  | s + 1, u => coreness_le_computeIndex (coreness_le_traj s u)
      fun v _ => by exact_mod_cast coreness_le_traj s v

/-- A vector `c ≥ coreness` in which every node with a positive value has a positive h-index. -/
theorem one_le_hIndex_of_coreness_le {c : V → ℕ} (hc : ∀ v, coreness G v ≤ c v)
    (hdeg : ∀ v, c v ≤ G.degree v) {u : V} (hu : c u ≠ 0) : 1 ≤ hIndex G (toE c) u := by
  have : 0 < G.degree u := by have := hdeg u; omega
  obtain ⟨v, hv⟩ := G.degree_pos_iff_exists_adj u |>.1 this
  refine one_le_hIndex hv ?_
  have := (one_le_coreness_of_adj hv.symm).trans (hc v)
  exact_mod_cast this

/-- A fixpoint of the update step above the coreness is the coreness. -/
theorem eq_coreness_of_step_eq {c : V → ℕ} (hc : ∀ v, coreness G v ≤ c v)
    (hdeg : ∀ v, c v ≤ G.degree v) (hfix : step G c = c) : c = coreness G := by
  funext u
  refine le_antisymm (le_coreness_of_le_hIndex (fun w => ?_) u) (hc u)
  by_cases hw : c w = 0
  · rw [hw]; exact Nat.zero_le _
  · exact le_hIndex_of_computeIndex_eq (congrFun hfix w)
      (Or.inl (one_le_hIndex_of_coreness_le hc hdeg hw))

/-- The coreness vector is a fixpoint of the update step (a consequence of Theorem 1). -/
theorem step_coreness : step G (coreness G) = coreness G := by
  funext u
  simp only [step]
  rw [computeIndex_eq, ← coreness_eq_hIndex]
  split_ifs with h
  · exact h.symm
  · omega

theorem traj_eq_coreness_of_succ_eq {s : ℕ} (h : traj G (s + 1) = traj G s) :
    traj G s = coreness G :=
  eq_coreness_of_step_eq (coreness_le_traj s) (traj_le_degree s) h

theorem traj_add_eq_coreness {s : ℕ} (h : traj G s = coreness G) (t : ℕ) :
    traj G (s + t) = coreness G := by
  induction t with
  | zero => exact h
  | succ t ih => rw [← add_assoc, traj_succ, ih, step_coreness]

/-- Potential argument: as long as the trajectory keeps changing, the total estimate drops by at
least one per step. -/
theorem add_sum_traj_le {s : ℕ} (h : ∀ t < s, traj G (t + 1) ≠ traj G t) :
    s + ∑ u, traj G s u ≤ ∑ u, G.degree u := by
  induction s with
  | zero => simp
  | succ s ih =>
    have ih := ih fun t ht => h t (by omega)
    have hlt : ∑ u, traj G (s + 1) u < ∑ u, traj G s u := by
      refine sum_lt_sum (fun u _ => traj_succ_le s u) ?_
      by_contra hne
      push Not at hne
      exact h s (by omega) (funext fun u => le_antisymm (traj_succ_le s u) (hne u (mem_univ u)))
    omega

/-- **Theorem 3 (Liveness), synchronous version.** The estimates eventually equal the corenesses. -/
theorem exists_traj_eq_coreness : ∃ s, traj G s = coreness G := by
  by_contra hne
  push Not at hne
  have := add_sum_traj_le (G := G) (s := ∑ u, G.degree u + 1) fun t _ heq =>
    hne t (traj_eq_coreness_of_succ_eq heq)
  omega

variable (G) in
/-- The number of update steps until all estimates are correct. -/
noncomputable def stab : ℕ := by
  classical exact Nat.find (exists_traj_eq_coreness (G := G))

theorem traj_stab : traj G (stab G) = coreness G := by
  classical
  unfold stab; convert Nat.find_spec (exists_traj_eq_coreness (G := G))

theorem traj_ne_coreness_of_lt {s : ℕ} (h : s < stab G) : traj G s ≠ coreness G := by
  classical
  unfold stab at h
  convert Nat.find_min (exists_traj_eq_coreness (G := G)) (by convert h)

theorem stab_le_of_traj_eq {s : ℕ} (h : traj G s = coreness G) : stab G ≤ s := by
  by_contra hlt; exact traj_ne_coreness_of_lt (not_le.1 hlt) h

theorem traj_eq_coreness_of_le {s : ℕ} (h : stab G ≤ s) : traj G s = coreness G := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  exact traj_add_eq_coreness traj_stab t

theorem traj_eq_coreness_iff {s : ℕ} : traj G s = coreness G ↔ stab G ≤ s :=
  ⟨stab_le_of_traj_eq, traj_eq_coreness_of_le⟩

theorem traj_succ_ne_of_lt {s : ℕ} (h : s < stab G) : traj G (s + 1) ≠ traj G s :=
  fun heq => traj_ne_coreness_of_lt h (traj_eq_coreness_of_succ_eq heq)

theorem traj_succ_eq_of_le {s : ℕ} (h : stab G ≤ s) : traj G (s + 1) = traj G s := by
  rw [traj_eq_coreness_of_le h, traj_eq_coreness_of_le (by omega)]

/-- The trajectory changes at step `s + 1` iff `s < stab G`. -/
theorem traj_succ_ne_iff {s : ℕ} : traj G (s + 1) ≠ traj G s ↔ s < stab G :=
  ⟨fun h => by by_contra h'; exact h (traj_succ_eq_of_le (not_lt.1 h')), traj_succ_ne_of_lt⟩

/-- The total initial error `Σ_u (d(u) − k(u))`. -/
theorem stab_le_sum : stab G ≤ ∑ u, (G.degree u - coreness G u) := by
  have h := add_sum_traj_le (G := G) (s := stab G) fun t ht => traj_succ_ne_of_lt ht
  rw [traj_stab] at h
  rw [sum_tsub_distrib _ fun u _ => coreness_le_degree u]
  omega

/-! ### Progress: at least one new correct node per step -/

variable (G) in
/-- `A(s)`: the nodes whose estimate is correct after `s` steps. -/
noncomputable def correctSet (s : ℕ) : Finset V := univ.filter fun u => traj G s u = coreness G u

theorem correctSet_mono (s : ℕ) : correctSet G s ⊆ correctSet G (s + 1) := by
  intro u hu
  simp only [correctSet, mem_filter, mem_univ, true_and] at hu ⊢
  exact le_antisymm ((traj_succ_le s u).trans hu.le) (coreness_le_traj _ u)

/-- A node of coreness `0` is isolated, hence always correct. -/
theorem traj_eq_of_coreness_eq_zero {s : ℕ} {u : V} (h : coreness G u = 0) :
    traj G s u = 0 := by
  have : G.degree u = 0 := by
    by_contra hd
    obtain ⟨v, hv⟩ := G.degree_pos_iff_exists_adj u |>.1 (Nat.pos_of_ne_zero hd)
    have := one_le_coreness_of_adj (G := G) hv; omega
  have := traj_le_degree (G := G) s u; omega

/-- **Progress lemma** (proof of Theorem 5): if some estimate is wrong after `s` steps, then after
`s + 1` steps some node that was wrong has become correct. -/
theorem progress {s : ℕ} (h : traj G s ≠ coreness G) :
    ∃ u, traj G s u ≠ coreness G u ∧ traj G (s + 1) u = coreness G u := by
  by_contra hcon
  push Not at hcon
  -- the set of wrong nodes and its minimal coreness `m`
  have hne : (univ.filter fun u => traj G s u ≠ coreness G u).Nonempty := by
    obtain ⟨u, hu⟩ := Function.ne_iff.1 h
    exact ⟨u, by simpa using hu⟩
  set W := univ.filter fun u => traj G s u ≠ coreness G u with hW
  obtain ⟨u₀, hu₀W, hu₀min⟩ := exists_min_image W (coreness G) hne
  set m := coreness G u₀ with hm
  have hu₀ : traj G s u₀ ≠ m := by simpa [W] using hu₀W
  -- `S` = nodes of coreness `≥ m+1` together with the wrong nodes of coreness `m`
  set S := univ.filter fun w => m + 1 ≤ coreness G w ∨ (w ∈ W ∧ coreness G w = m)
  have hS : IsCoreSet G (m + 1) S := by
    intro w hw
    simp only [S, mem_filter, mem_univ, true_and] at hw
    rcases hw with hw | ⟨hwW, hwm⟩
    · refine (isCoreSet_kCore G (m + 1) w (le_coreness_iff.1 hw)).trans
        (card_filter_adj_mono (fun v hv => ?_) w)
      simp only [S, mem_filter, mem_univ, true_and]
      exact Or.inl (le_coreness_iff.2 hv)
    · have hwW' : traj G s w ≠ coreness G w := by simpa [W] using hwW
      have hm0 : m ≠ 0 := by
        intro h0
        exact hwW' (by rw [traj_eq_of_coreness_eq_zero (hwm.trans h0)]; omega)
      have hstep := hcon w hwW'
      have hge := coreness_le_traj (G := G) (s + 1) w
      have hgt : m + 1 ≤ traj G (s + 1) w := by omega
      -- so the h-index of `w` is at least `m + 1`
      have hh : m + 1 ≤ hIndex G (toE (traj G s)) w := by
        rw [traj_succ_apply, computeIndex_eq] at hgt
        split_ifs at hgt <;> omega
      refine (le_hIndex_iff.1 hh).trans (card_le_card fun v hv => ?_)
      simp only [mem_filter, SimpleGraph.mem_neighborFinset, Nat.cast_le] at hv
      simp only [S, mem_filter, mem_univ, true_and]
      refine ⟨?_, hv.1⟩
      by_cases hvW : v ∈ W
      · have := hu₀min v hvW
        rcases Nat.lt_or_ge m (coreness G v) with hlt | hle
        · exact Or.inl hlt
        · exact Or.inr ⟨hvW, by omega⟩
      · have hv' : traj G s v = coreness G v := by simpa [W] using hvW
        exact Or.inl (hv' ▸ hv.2)
  have := le_coreness_of_isCoreSet hS (u := u₀) (by
    simp only [S, mem_filter, mem_univ, true_and]; exact Or.inr ⟨hu₀W, rfl⟩)
  omega

theorem card_correctSet_lt {s : ℕ} (h : s < stab G) :
    #(correctSet G s) < #(correctSet G (s + 1)) := by
  obtain ⟨u, hu, hu'⟩ := progress (traj_ne_coreness_of_lt h)
  refine card_lt_card ⟨correctSet_mono s, fun hsub => hu ?_⟩
  have := hsub (by simp [correctSet, hu'] : u ∈ correctSet G (s + 1))
  simpa [correctSet] using this

theorem card_correctSet_ge {s : ℕ} (h : s ≤ stab G) :
    #(correctSet G 0) + s ≤ #(correctSet G s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have := card_correctSet_lt (G := G) (s := s) (by omega)
    have := ih (by omega); omega

/-- `stab G ≤ N − |{u : d(u) = k(u)}|`. -/
theorem stab_le_card_sub : stab G ≤ Fintype.card V - #(correctSet G 0) := by
  have h1 := card_correctSet_ge (G := G) le_rfl
  have h2 : #(correctSet G (stab G)) ≤ Fintype.card V := card_le_univ _
  omega

/-- Nodes of minimum degree have coreness equal to their degree. -/
theorem coreness_eq_degree_of_minDegree {u : V} (hu : G.degree u = G.minDegree) :
    coreness G u = G.degree u := by
  refine le_antisymm (coreness_le_degree u) ?_
  rw [hu]
  refine le_coreness_of_isCoreSet (S := univ) (fun w _ => ?_) (mem_univ u)
  have : #{v ∈ (univ : Finset V) | G.Adj w v} = G.degree w := by
    rw [← G.card_neighborFinset_eq_degree]; congr 1; ext; simp
  rw [this]; exact G.minDegree_le_degree w

variable (G) in
/-- `K`: the number of nodes of minimum degree. -/
noncomputable def numMinDegree : ℕ := #(univ.filter fun u : V => G.degree u = G.minDegree)

theorem numMinDegree_le_card_correctSet_zero : numMinDegree G ≤ #(correctSet G 0) := by
  refine card_le_card fun u hu => ?_
  simp only [mem_filter, mem_univ, true_and] at hu
  rw [correctSet, mem_filter]
  exact ⟨mem_univ _, (coreness_eq_degree_of_minDegree hu).symm⟩

theorem stab_le_card_sub_minDegree : stab G ≤ Fintype.card V - numMinDegree G :=
  stab_le_card_sub.trans (Nat.sub_le_sub_left numMinDegree_le_card_correctSet_zero _)

theorem one_le_numMinDegree [Nonempty V] : 1 ≤ numMinDegree G := by
  obtain ⟨u, hu⟩ := G.exists_minimal_degree_vertex
  exact card_pos.2 ⟨u, by simp [hu]⟩

end KCoreDecomposition
