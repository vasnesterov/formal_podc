import Papers.PODC2016.DynamicMIS.Alg2Roots

/-!
# Algorithm 2 after a non-abrupt change (Lemmas 8, 9, 11)

Edge insertion/deletion, graceful node deletion and node unmuting (`netOf`, `initOf`): with
`S = infl c cfg r` the set of influenced nodes,

* `graceful_eq_of_notMem_infl`: only nodes of `S` ever change their state;
* `graceful_stableFrom`, `graceful_run_eq`: the run is stable from round `3|S|` on, and then equals
  the greedy MIS of the new configuration (`…_add_two`: the paper's bound `3|S| + 2`);
* `graceful_changes_le_three` (**Lemma 8**): every node changes its visible state at most three
  times; `graceful_broadcasts_le` (**Lemma 9**): the total number of broadcasts is at most `3|S|`.

The first section packages the abstract results (`Alg2Basic`, `Alg2Rounds`, `Alg2Roots`) for an
arbitrary set `X` closed under the two rules of recursion (1) (`run_eq_of_notMem`, `correct`).
-/

open Finset SimpleGraph

namespace DynamicMIS

namespace Alg2

variable {V : Type*}

section General

variable {N : Net V} {c₀ : V → St}

/-- **Only nodes of `X` change**, if `X` contains the initially-`C` nodes and is closed under the
two rules of recursion (1): a node in `M` with a predecessor in `X`, and a node in `M̄` with a
predecessor in `X` all of whose `M`-predecessors are in `X`. -/
theorem run_eq_of_notMem (h₀ : InitOK N c₀) (X : Set V)
    (hC : ∀ v ∈ N.part, c₀ v = .changing 0 → v ∈ X)
    (hM : ∀ v ∈ N.part, c₀ v = .inM → ∀ u, N.Pred u v → u ∈ X → v ∈ X)
    (hMbar : ∀ v ∈ N.part, c₀ v = .outM → (∃ u, N.Pred u v ∧ u ∈ X) →
      (∀ u, N.Pred u v → c₀ u = .inM → u ∈ X) → v ∈ X) :
    ∀ t v, v ∉ X → run N c₀ t v = c₀ v := by
  intro t
  induction t with
  | zero => intros; rfl
  | succ t ih =>
    intro v hvX
    by_cases hv : v ∈ N.part
    swap
    · exact run_of_notMem hv _
    -- a predecessor that has just changed to `C` is in `X`
    have hCX : ∀ u, N.Pred u v → run N c₀ t u = .changing 0 → u ∈ X := fun u hu hu0 =>
      by_contra fun huX => by
        rw [ih u huX] at hu0
        exact huX (hC u hu.2.1 hu0)
    rcases h₀ v hv with hf | h0
    · rcases St.isFinal_iff.1 hf with hM' | hM'
      · rw [run_succ, step_of_inM N _ hv (by rw [ih v hvX, hM']), hM']
        refine ite_eq_right fun ⟨u, hu, hu0⟩ => hvX (hM v hv hM' u hu (hCX u hu hu0))
      · rw [run_succ, step_of_outM N _ hv (by rw [ih v hvX, hM']), hM']
        refine ite_eq_right fun ⟨⟨u, hu, hu0⟩, hno⟩ => hvX (hMbar v hv hM' ⟨u, hu, hCX u hu hu0⟩
          fun w hw hwM => by_contra fun hwX => hno w hw (by rw [ih w hwX, hwM]))
    · exact absurd (hC v hv h0) hvX

/-- Under the same hypotheses, every participating node that is ever outside `M`/`M̄` is in `X`. -/
theorem mem_of_not_isFinal [Fintype V] (h₀ : InitOK N c₀) (X : Set V)
    (hC : ∀ v ∈ N.part, c₀ v = .changing 0 → v ∈ X)
    (hM : ∀ v ∈ N.part, c₀ v = .inM → ∀ u, N.Pred u v → u ∈ X → v ∈ X)
    (hMbar : ∀ v ∈ N.part, c₀ v = .outM → (∃ u, N.Pred u v ∧ u ∈ X) →
      (∀ u, N.Pred u v → c₀ u = .inM → u ∈ X) → v ∈ X) :
    ∀ t, ∀ v ∈ N.part, ¬ (run N c₀ t v).IsFinal → v ∈ (Set.toFinite X).toFinset := by
  intro t v hv hnf
  rw [Set.Finite.mem_toFinset]
  by_contra hvX
  rw [run_eq_of_notMem h₀ X hC hM hMbar t v hvX] at hnf
  rcases h₀ v hv with h | h
  · exact hnf h
  · exact hvX (hC v hv h)

/-- Packaging of correctness, stabilisation and the round bound for a closed set `X`. -/
theorem correct [Fintype V] (h₀ : InitOK N c₀) (hInv : Inv N c₀) (hA : N.active ⊆ N.part)
    (X : Set V)
    (hC : ∀ v ∈ N.part, c₀ v = .changing 0 → v ∈ X)
    (hM : ∀ v ∈ N.part, c₀ v = .inM → ∀ u, N.Pred u v → u ∈ X → v ∈ X)
    (hMbar : ∀ v ∈ N.part, c₀ v = .outM → (∃ u, N.Pred u v ∧ u ∈ X) →
      (∀ u, N.Pred u v → c₀ u = .inM → u ∈ X) → v ∈ X) :
    StableFrom N c₀ (3 * X.ncard) ∧
      ∀ v ∈ N.part, run N c₀ (3 * X.ncard) v = ofSet (N.graph.greedyMIS N.active N.rank) v := by
  have hX' := mem_of_not_isFinal h₀ X hC hM hMbar
  have hcard : X.ncard = #(Set.toFinite X).toFinset := Set.ncard_eq_toFinset_card X
  rw [hcard]
  exact ⟨stableFrom_three_mul h₀ hX', (hInv.run _).eq_ofSet hA (isFinal_run_three_mul h₀ hX')⟩

/-- Every `C`-entry of a node happens before time `|X|`, if `X` contains every node that is ever
outside `M`/`M̄`. -/
theorem entries_lt {X : Finset V}
    (hX : ∀ t, ∀ v ∈ N.part, ¬ (run N c₀ t v).IsFinal → v ∈ X) {v : V} (hv : v ∈ N.part)
    {T : ℕ} : ∀ t ∈ entries N c₀ v T, t + 1 ≤ #X := by
  intro t ht
  simp only [entries, mem_filter] at ht
  have h1 := entry_le hX t v hv ht.2
  have h2 := cntLow_add_one_le (r := N.rank) (hX t v hv (by rw [ht.2]; simp))
  omega

/-- **Lemma 12 + Lemma 11**: the number of `C`-entries of a node is at most `log₃ (|X| + 1) + 1`. -/
theorem card_entries_le_log {X : Finset V}
    (hX : ∀ t, ∀ v ∈ N.part, ¬ (run N c₀ t v).IsFinal → v ∈ X) {v : V} (hv : v ∈ N.part)
    (T : ℕ) : #(entries N c₀ v T) ≤ Nat.log 3 (#X + 1) + 1 := by
  rcases Nat.eq_zero_or_pos #X with h0 | h0
  · have : entries N c₀ v T = ∅ := by
      refine eq_empty_of_forall_notMem fun t ht => ?_
      have := entries_lt hX hv t ht
      omega
    rw [this]; simp
  · have := card_le_log (entries N c₀ v T) (#X - 1)
      (fun t ht => by have := entries_lt hX hv t ht; omega)
      (fun a ha b hb hab => by
        simp only [entries, mem_filter] at ha hb
        exact entry_spacing hv ha.2 hb.2 hab)
    rwa [show #X - 1 + 2 = #X + 1 by omega] at this

end General

/-! ### The non-abrupt changes -/

section Graceful

variable [DecidableEq V] {c : Change V} {cfg : Config V} {r : V → ℕ}

/-- The MIS invariant breaks at `v*`. -/
abbrev Broken (c : Change V) (cfg : Config V) (r : V → ℕ) : Prop :=
  ¬ InvariantAt (c.apply cfg).graph (c.apply cfg).nodes r (cfg.graph.greedyMIS cfg.nodes r)
    (c.vStar r)

theorem initOf_eq_changing_iff {v : V} :
    initOf c cfg r v = .changing 0 ↔ v = c.vStar r ∧ Broken c cfg r := by
  unfold initOf ofSet
  split_ifs with h1 h2 <;> simp_all [Broken]

theorem initOf_eq_inM_iff {v : V} :
    initOf c cfg r v = .inM ↔ ¬ (v = c.vStar r ∧ Broken c cfg r) ∧
      v ∈ cfg.graph.greedyMIS cfg.nodes r := by
  unfold initOf ofSet
  split_ifs with h1 h2 <;> simp_all [Broken]

theorem initOf_eq_outM_iff {v : V} :
    initOf c cfg r v = .outM ↔ ¬ (v = c.vStar r ∧ Broken c cfg r) ∧
      v ∉ cfg.graph.greedyMIS cfg.nodes r := by
  unfold initOf ofSet
  split_ifs with h1 h2 <;> simp_all [Broken]

theorem initOf_cases (v : V) : initOf c cfg r v = .changing 0 ∨ initOf c cfg r v = .inM ∨
    initOf c cfg r v = .outM := by
  unfold initOf ofSet
  split_ifs <;> simp

theorem initOK_initOf : InitOK (netOf c cfg r) (initOf c cfg r) := fun v _ => by
  rcases initOf_cases (c := c) (cfg := cfg) (r := r) v with h | h | h <;> simp [h]

theorem greedyMIS_subset_baseNodes :
    cfg.graph.greedyMIS cfg.nodes r ⊆ c.baseNodes cfg :=
  fun _ h => Or.inl (greedyMIS_subset _ _ _ h)

/-- The invariants (J0)–(J2) hold initially. -/
theorem inv_initOf (hr : Function.Injective r) : Inv (netOf c cfg r) (initOf c cfg r) := by
  have hd := flipData c cfg hr
  set s := cfg.graph.greedyMIS cfg.nodes r with hs
  refine ⟨fun v hv hva hM => ?_, fun v hv hM u hu => ?_, fun v hv hva hM => ?_⟩
  · obtain ⟨h1, h2⟩ := initOf_eq_inM_iff.1 hM
    change v ∉ (c.apply cfg).nodes at hva
    by_cases hvs : v = c.vStar r
    · subst hvs
      have hinv : InvariantAt (c.apply cfg).graph (c.apply cfg).nodes r s (c.vStar r) :=
        by_contra fun h => h1 ⟨rfl, h⟩
      exact hva (hinv.1 h2).1
    · exact hva ((hd.nodes_new v hvs).2 ((hd.nodes_old v hvs).1 (greedyMIS_subset _ _ _ h2)))
  · obtain ⟨h1, h2⟩ := initOf_eq_inM_iff.1 hM
    obtain ⟨hadj, -, hlt⟩ := hu
    by_cases hb : u = c.vStar r ∧ Broken c cfg r
    · exact Or.inr (initOf_eq_changing_iff.2 hb)
    refine Or.inl (initOf_eq_outM_iff.2 ⟨hb, ?_⟩)
    by_cases hvs : v = c.vStar r
    · subst hvs
      have hinv : InvariantAt (c.apply cfg).graph (c.apply cfg).nodes r s (c.vStar r) :=
        by_contra fun h => h1 ⟨rfl, h⟩
      exact (hinv.1 h2).2 u hadj hlt
    · have := (hd.pred_old v hvs u).2 ((hd.pred_new v hvs u).1 ⟨hadj, hlt⟩)
      exact ((greedyMIS_iff _ _ _).1 h2).2 u this.1 hlt
  · obtain ⟨h1, h2⟩ := initOf_eq_outM_iff.1 hM
    change v ∈ (c.apply cfg).nodes at hva
    have : ∃ w, (c.apply cfg).graph.Adj w v ∧ r w < r v ∧ w ∈ s := by
      by_cases hvs : v = c.vStar r
      · subst hvs
        have hinv : InvariantAt (c.apply cfg).graph (c.apply cfg).nodes r s (c.vStar r) :=
          by_contra fun h => h1 ⟨rfl, h⟩
        have := mt hinv.2 h2
        push Not at this
        obtain ⟨w, hw1, hw2, hw3⟩ := this hva
        exact ⟨w, hw1, hw2, hw3⟩
      · have hvA : v ∈ cfg.nodes := (hd.nodes_old v hvs).2 ((hd.nodes_new v hvs).1 hva)
        obtain ⟨w, hw, hadj, hlt⟩ := greedyMIS_maximal _ _ _ hvA h2
        have := (hd.pred_new v hvs w).2 ((hd.pred_old v hvs w).1 ⟨hadj, hlt⟩)
        exact ⟨w, this.1, hlt, hw⟩
    obtain ⟨w, hadj, hlt, hw⟩ := this
    refine ⟨w, ⟨hadj, greedyMIS_subset_baseNodes hw, hlt⟩, ?_⟩
    by_cases hb : w = c.vStar r ∧ Broken c cfg r
    · exact Or.inr (initOf_eq_changing_iff.2 hb)
    · exact Or.inl (initOf_eq_inM_iff.2 ⟨hb, hw⟩)

theorem infl_of_broken (h : Broken c cfg r) : infl c cfg r =
    {u | Influenced (c.apply cfg).graph (c.baseNodes cfg) r (cfg.graph.greedyMIS cfg.nodes r)
      (c.vStar r) u} := by
  simp only [infl]; exact ite_eq_right h

/-- The influenced set `S` is closed under the rules used by `run_eq_of_notMem`. -/
theorem infl_closed :
    (∀ v ∈ (netOf c cfg r).part, initOf c cfg r v = .changing 0 → v ∈ infl c cfg r) ∧
    (∀ v ∈ (netOf c cfg r).part, initOf c cfg r v = .inM → ∀ u, (netOf c cfg r).Pred u v →
      u ∈ infl c cfg r → v ∈ infl c cfg r) ∧
    (∀ v ∈ (netOf c cfg r).part, initOf c cfg r v = .outM →
      (∃ u, (netOf c cfg r).Pred u v ∧ u ∈ infl c cfg r) →
      (∀ u, (netOf c cfg r).Pred u v → initOf c cfg r u = .inM → u ∈ infl c cfg r) →
      v ∈ infl c cfg r) := by
  by_cases hb : Broken c cfg r
  · rw [infl_of_broken hb]
    refine ⟨fun v _ h => ?_, fun v hv h u ⟨hadj, _, hlt⟩ hu => ?_, fun v hv h _ hall => ?_⟩
    · obtain ⟨rfl, -⟩ := initOf_eq_changing_iff.1 h
      exact Influenced.base
    · exact Influenced.inM hv (initOf_eq_inM_iff.1 h).2 hadj hlt hu
    · refine Influenced.inMbar hv (initOf_eq_outM_iff.1 h).2 fun w hadj hlt hw => ?_
      by_cases hwb : w = c.vStar r ∧ Broken c cfg r
      · rw [hwb.1]; exact Influenced.base
      · exact hall w ⟨hadj, greedyMIS_subset_baseNodes hw, hlt⟩ (initOf_eq_inM_iff.2 ⟨hwb, hw⟩)
  · rw [infl_eq_empty (not_not.1 hb)]
    refine ⟨fun v _ h => absurd (initOf_eq_changing_iff.1 h).2 hb, fun _ _ _ _ _ h => h.elim,
      fun _ _ _ ⟨_, _, h⟩ _ => h.elim⟩

variable (hr : Function.Injective r)
include hr

omit hr in
/-- **Only influenced nodes change their state** (non-abrupt changes). -/
theorem graceful_eq_of_notMem_infl :
    ∀ t v, v ∉ infl c cfg r → run (netOf c cfg r) (initOf c cfg r) t v = initOf c cfg r v :=
  run_eq_of_notMem initOK_initOf _ infl_closed.1 infl_closed.2.1 infl_closed.2.2

theorem graceful_correct [Fintype V] :
    StableFrom (netOf c cfg r) (initOf c cfg r) (3 * (infl c cfg r).ncard) ∧
      ∀ v ∈ (netOf c cfg r).part, run (netOf c cfg r) (initOf c cfg r) (3 * (infl c cfg r).ncard) v =
        ofSet ((c.apply cfg).graph.greedyMIS (c.apply cfg).nodes r) v :=
  correct initOK_initOf (inv_initOf hr) (fun _ h => Or.inr h) _ infl_closed.1 infl_closed.2.1
    infl_closed.2.2

/-- **Lemma 11 (non-abrupt changes): stabilisation.** The run is stable from round `3|S|`. -/
theorem graceful_stableFrom [Fintype V] :
    StableFrom (netOf c cfg r) (initOf c cfg r) (3 * (infl c cfg r).ncard) :=
  (graceful_correct hr).1

/-- **Correctness (non-abrupt changes).** After `3|S|` rounds the states are those of the greedy
MIS of the new configuration. -/
theorem graceful_run_eq [Fintype V] :
    run (netOf c cfg r) (initOf c cfg r) (3 * (infl c cfg r).ncard) =
      ofSet ((c.apply cfg).graph.greedyMIS (c.apply cfg).nodes r) := by
  funext v
  by_cases hv : v ∈ (netOf c cfg r).part
  · exact (graceful_correct hr).2 v hv
  · rw [run_of_notMem hv]
    have h1 : initOf c cfg r v = .outM := by
      rcases initOf_cases (c := c) (cfg := cfg) (r := r) v with h | h | h
      · obtain ⟨rfl, hb⟩ := initOf_eq_changing_iff.1 h
        exact absurd (Or.inl ((flipData c cfg hr).rule hb).1 |>.elim id id) hv
      · exact absurd (greedyMIS_subset_baseNodes (initOf_eq_inM_iff.1 h).2) hv
      · exact h
    rw [h1, ofSet, ite_eq_right]
    exact fun h => hv (Or.inr (greedyMIS_subset _ _ _ h))

/-- The paper's bound: stable from round `3|S| + 2`, with the new greedy MIS. -/
theorem graceful_stableFrom_add_two [Fintype V] :
    StableFrom (netOf c cfg r) (initOf c cfg r) (3 * (infl c cfg r).ncard + 2) ∧
      run (netOf c cfg r) (initOf c cfg r) (3 * (infl c cfg r).ncard + 2) =
        ofSet ((c.apply cfg).graph.greedyMIS (c.apply cfg).nodes r) := by
  have h := graceful_stableFrom hr (c := c) (cfg := cfg)
  refine ⟨fun t ht => (h t (by omega)).trans (h _ (by omega)).symm, ?_⟩
  rw [h _ (by omega), graceful_run_eq hr]

omit hr in
/-- After a non-abrupt change, at most one node (`v*`) is in `C` initially. -/
theorem card_initC_initOf_le [Fintype V] : #(initC (netOf c cfg r) (initOf c cfg r)) ≤ 1 := by
  refine card_le_one.2 fun a ha b hb => ?_
  simp only [initC, mem_filter, mem_univ, true_and] at ha hb
  rw [(initOf_eq_changing_iff.1 ha.2).1, (initOf_eq_changing_iff.1 hb.2).1]

omit hr in
/-- **Lemma 8.** After a non-abrupt change, every node changes its visible state at most three
times (`M`/`M̄` → `C` → `R` → `M`/`M̄`), over any number of rounds. -/
theorem graceful_changes_le_three [Fintype V] (v : V) (T : ℕ) :
    changes (netOf c cfg r) (initOf c cfg r) v T ≤ 3 := by
  by_cases hv : v ∈ (netOf c cfg r).part
  · have h1 := changes_le (initOK_initOf (c := c) (cfg := cfg) (r := r)) v T
    have h2 := card_entries_le_initC hv T (c₀ := initOf c cfg r)
    have h3 := card_initC_initOf_le (c := c) (cfg := cfg) (r := r)
    omega
  · rw [changes_of_notMem hv]; omega

omit hr in
/-- **Lemma 9 (broadcasts).** After a non-abrupt change, the total number of broadcasts is at
most `3|S|`. -/
theorem graceful_broadcasts_le [Fintype V] (T : ℕ) :
    ∑ t ∈ range T, broadcastsAt (netOf c cfg r) (initOf c cfg r) t ≤ 3 * (infl c cfg r).ncard := by
  have := sum_broadcastsAt_le initOK_initOf (Set.toFinite (infl c cfg r)).toFinset
    (fun v hv t => graceful_eq_of_notMem_infl t v (by simpa using hv)) 1 T
    (fun v _ hvP => (card_entries_le_initC hvP T).trans card_initC_initOf_le)
  rwa [mul_one, ← Set.ncard_eq_toFinset_card] at this

end Graceful

end Alg2

end DynamicMIS
