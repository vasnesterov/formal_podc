import Papers.PODC2025.GraphAlgorithmsPredictions.Greedy

/-!
# MIS with predictions: pruning, error measure, consistency and `η`-degradation

Sections 3–5 of Boyar–Ellen–Larsen (PODC 2025 BA).

* `pruneSet G x`: the set `I` of the 3-round pruning algorithm (prediction 1, all neighbours
  prediction 0); `pruneSet'`: the variant "prediction 1 and all neighbours with prediction 1 have
  smaller identifiers". Both are independent, hence extendable (`pruneSet_extendable`,
  `pruneSet'_extendable`), and `pruneSet ⊆ pruneSet'`.
* `pruneAlg_status`: after 3 rounds of the pruning algorithm, the nodes of `I` output 1, their
  neighbours output 0, and the remainder (the union of the *error components*) is active.
* `eta G x`: the error measure `η` = the maximum number of nodes of an error component.
* `predAlg_consistent`: if the prediction is an MIS, then `η = 0` and the algorithm outputs the
  prediction after 3 rounds (consistency `c(n) = 3`).
* `predAlg_correct`: in general, every node has terminated after `η + 3` rounds and the output is an
  MIS (`η`-degrading).
* `greedy_round_complexity`: the Distributed Greedy MIS Algorithm alone terminates within `n` rounds
  on an `n`-node graph (without predictions).
* `predAlg_isLocal`: the algorithm is a LOCAL algorithm (its state after `t` rounds is `t`-local).
-/

namespace Podc.GraphAlgorithmsPredictions

open SimpleGraph Cslib.LocallyIterative

variable {V : Type*} [LinearOrder V] (G : SimpleGraph V) (x : V → Bool)

/-! ### The pruning sets and extendability -/

/-- The set `I` of the pruning algorithm: nodes with prediction 1 whose neighbours all have
prediction 0. -/
def pruneSet : Set V := {v | x v = true ∧ ∀ u, G.Adj v u → x u = false}

/-- The variant of Section 3: nodes with prediction 1 whose neighbours with prediction 1 (if any)
all have smaller identifiers. -/
def pruneSet' : Set V := {v | x v = true ∧ ∀ u, G.Adj v u → x u = true → u < v}

omit [LinearOrder V] in
lemma pruneSet_indep : G.IsIndepSet (pruneSet G x) := by
  intro u hu w hw _ hadj
  have := hu.2 w hadj
  rw [hw.1] at this
  cases this

lemma pruneSet'_indep : G.IsIndepSet (pruneSet' G x) := by
  intro u hu w hw _ hadj
  exact absurd (hu.2 w hadj hw.1) (not_lt.2 (hw.2 u hadj.symm hu.1).le)

lemma pruneSet_subset_pruneSet' : pruneSet G x ⊆ pruneSet' G x := by
  intro v hv
  refine ⟨hv.1, fun u hadj hu => ?_⟩
  rw [hv.2 u hadj] at hu
  cases hu

omit [LinearOrder V] in
/-- Section 3: the partial solution of the pruning algorithm agrees with the prediction: nodes of `I`
have prediction 1 and their neighbours (which output 0) have prediction 0. -/
theorem pruneSet_agrees {u v : V} (hu : u ∈ pruneSet G x) (hadj : G.Adj u v) :
    x u = true ∧ x v = false :=
  ⟨hu.1, hu.2 v hadj⟩

omit [LinearOrder V] in
/-- Section 3: the partial solution of the pruning algorithm (`I` outputs 1, `N(I)` outputs 0) is
extendable, and it agrees with the prediction on `I`. -/
theorem pruneSet_extendable {M : Set V} (hM : IsMISOn G (remainder G (pruneSet G x)) M) :
    IsMIS G (pruneSet G x ∪ M) :=
  isMIS_union_of_extendable (pruneSet_indep G x) hM

/-- Section 3: the variant initialization also produces an extendable partial solution. -/
theorem pruneSet'_extendable {M : Set V} (hM : IsMISOn G (remainder G (pruneSet' G x)) M) :
    IsMIS G (pruneSet' G x ∪ M) :=
  isMIS_union_of_extendable (pruneSet'_indep G x) hM

omit [LinearOrder V] in
/-- If the prediction is an MIS, the pruning algorithm selects exactly the predicted set and
nothing remains. -/
theorem pruneSet_of_isMIS (hx : IsMIS G {v | x v = true}) :
    pruneSet G x = {v | x v = true} ∧ remainder G (pruneSet G x) = ∅ := by
  have h1 : pruneSet G x = {v | x v = true} := by
    ext v
    refine ⟨fun h => h.1, fun h => ⟨h, fun u hadj => ?_⟩⟩
    by_contra hu
    exact hx.1 h (by simpa using hu) (G.ne_of_adj hadj) hadj
  refine ⟨h1, Set.eq_empty_of_forall_notMem fun v hv => ?_⟩
  rw [h1] at hv
  obtain ⟨u, hu, hadj⟩ := hx.2 v hv.1
  exact hv.2 u hu hadj

/-! ### The error measure -/

variable [Fintype V]

/-- The error measure `η` (Section 3): the maximum number of nodes of an error component, i.e. of a
connected component of the subgraph induced by the nodes left active by the pruning algorithm. -/
noncomputable def eta : ℕ :=
  open Classical in
  Finset.univ.sup fun v =>
    if v ∈ remainder G (pruneSet G x) then (comp G (remainder G (pruneSet G x)) v).card else 0

lemma comp_card_le_eta {v : V} (hv : v ∈ remainder G (pruneSet G x)) :
    (comp G (remainder G (pruneSet G x)) v).card ≤ eta G x := by
  classical
  have := Finset.le_sup (f := fun v =>
    if v ∈ remainder G (pruneSet G x) then (comp G (remainder G (pruneSet G x)) v).card else 0)
    (Finset.mem_univ v)
  simpa [eta, hv] using this

omit [Fintype V] in
lemma eta_eq_zero_of_isMIS (hx : IsMIS G {v | x v = true}) [Fintype V] : eta G x = 0 := by
  classical
  simp [eta, (pruneSet_of_isMIS G x hx).2]

/-! ### Three rounds of pruning -/

omit [LinearOrder V] [Fintype V] in
open Classical in
/-- Status after the pruning algorithm. -/
noncomputable def pruneStatus (v : V) : Status :=
  if v ∈ pruneSet G x then .inMIS
  else if v ∈ remainder G (pruneSet G x) then .active else .outMIS

omit [LinearOrder V] [Fintype V] in
lemma pruneStatus_eq_inMIS_iff {v : V} : pruneStatus G x v = .inMIS ↔ v ∈ pruneSet G x := by
  classical
  unfold pruneStatus
  split_ifs with a b <;> simp [a]

omit [LinearOrder V] [Fintype V] in
lemma pruneStatus_eq_active_iff {v : V} :
    pruneStatus G x v = .active ↔ v ∈ remainder G (pruneSet G x) := by
  classical
  unfold pruneStatus
  split_ifs with a b
  · simp only [false_iff]; exact fun h => h.1 a
  · simp [b]
  · simp [b]

omit [LinearOrder V] [Fintype V] in
lemma pruneStatus_eq_outMIS_iff {v : V} :
    pruneStatus G x v = .outMIS ↔ v ∉ pruneSet G x ∧ v ∉ remainder G (pruneSet G x) := by
  classical
  unfold pruneStatus
  split_ifs with a b <;> simp_all

omit [LinearOrder V] [Fintype V] in
lemma initSt_id [LinearOrder V] (v : V) : (initSt x v).id = v := rfl

omit [Fintype V] in
/-- **Section 3**: after rounds 1–3 of the pruning algorithm, the nodes of `I` have output 1, their
neighbours have output 0, and exactly the remainder is active. -/
theorem pruneAlg_status (v : V) : status G pruneRule (initSt x) 3 v = pruneStatus G x v := by
  classical
  have s1 : ∀ v, status G pruneRule (initSt x) 1 v =
      if v ∈ pruneSet G x then .inMIS else .active := by
    intro v
    rw [status_succ_prune (t := 0) rfl]
    simp only [status, Algorithm.run_zero, initSt, true_and]
    by_cases hv : v ∈ pruneSet G x
    · rw [ite_eq_left hv]; exact ite_eq_left hv
    · rw [ite_eq_right hv]; exact ite_eq_right hv
  have s2 : ∀ v, status G pruneRule (initSt x) 2 v = pruneStatus G x v := by
    intro v
    rw [status_succ_out (t := 1) rfl, s1]
    simp only [pruneStatus]
    by_cases hv : v ∈ pruneSet G x
    · simp [hv]
    · have : (∃ u, G.Adj v u ∧ status G pruneRule (initSt x) 1 u = .inMIS) ↔
          v ∉ remainder G (pruneSet G x) := by
        simp only [s1, remainder, Set.mem_ofPred_eq, hv, not_false_eq_true, true_and,
          not_forall, not_not]
        constructor
        · rintro ⟨u, hadj, hu⟩
          refine ⟨u, ?_, hadj⟩
          by_contra h
          simp [h] at hu
        · rintro ⟨u, hu, hadj⟩
          exact ⟨u, hadj, by simp [hu]⟩
      simp only [hv, ↓reduceIte, true_and, this]
      by_cases hr : v ∈ remainder G (pruneSet G x) <;> simp [hr]
  rw [status_succ_out (t := 2) rfl, s2]
  by_cases h : pruneStatus G x v = .active ∧
      ∃ u, G.Adj v u ∧ status G pruneRule (initSt x) 2 u = .inMIS
  · exfalso
    obtain ⟨h1, u, hadj, hu⟩ := h
    rw [s2, pruneStatus_eq_inMIS_iff] at hu
    rw [pruneStatus_eq_active_iff] at h1
    exact h1.2 u hu hadj
  · exact ite_eq_right h

/-! ### The algorithm with predictions -/

/-- Status of node `v` after `t` rounds of the MIS algorithm with predictions. -/
noncomputable def predStatus (t : ℕ) (v : V) : Status :=
  (predAlg.run G (initSt x) t v).status

omit [Fintype V] in
/-- The configuration after pruning. -/
lemma predStatus_add (t : ℕ) (v : V) :
    predStatus G x (3 + t) v = status G greedyRule (pruneAlg.run G (initSt x) 3) t v := by
  simp only [predStatus, predAlg, Algorithm.run_seq_add]
  rfl

omit [Fintype V] in
lemma pruneRun_id (v : V) : (pruneAlg.run G (initSt x) 3 v).id = v :=
  run_id G pruneRule (initSt_id x) 3 v

omit [Fintype V] in
lemma greedy_start (v : V) :
    status G greedyRule (pruneAlg.run G (initSt x) 3) 0 v = pruneStatus G x v :=
  pruneAlg_status G x v

omit [Fintype V] in
lemma greedy_start_inv :
    Indep G (status G greedyRule (pruneAlg.run G (initSt x) 3) 0) ∧
    OutDom G (status G greedyRule (pruneAlg.run G (initSt x) 3) 0) ∧
    Clean G (status G greedyRule (pruneAlg.run G (initSt x) 3) 0) := by
  simp only [Indep, OutDom, Clean, greedy_start, pruneStatus_eq_inMIS_iff,
    pruneStatus_eq_active_iff, pruneStatus_eq_outMIS_iff]
  refine ⟨fun u w hadj hu hw => pruneSet_indep G x hu ((pruneStatus_eq_inMIS_iff G x).1 hw)
      (G.ne_of_adj hadj) hadj,
    fun v hv => ?_, fun v hv u hadj hu => hv.2 u ((pruneStatus_eq_inMIS_iff G x).1 hu) hadj⟩
  obtain ⟨a, b⟩ := hv
  simp only [remainder, Set.mem_ofPred_eq, a, not_false_eq_true, true_and, not_forall,
    not_not] at b
  obtain ⟨u, hu, hadj⟩ := b
  exact ⟨u, hadj, hu⟩

omit [Fintype V] in
lemma greedy_start_active :
    {y | status G greedyRule (pruneAlg.run G (initSt x) 3) 0 y = .active} =
      remainder G (pruneSet G x) := by
  ext v
  simp only [Set.mem_ofPred_eq, greedy_start, pruneStatus_eq_active_iff]

/-- **Section 5 (`η`-degradation)**: running the pruning algorithm and then the Distributed Greedy
MIS Algorithm (on every error component), every node has terminated after `η + 3` rounds. -/
theorem predAlg_terminates {t : ℕ} (ht : eta G x + 3 ≤ t) (v : V) : predStatus G x t v ≠ .active := by
  obtain ⟨s, rfl⟩ : ∃ s, t = 3 + s := ⟨t - 3, by omega⟩
  rw [predStatus_add]
  by_cases h0 : status G greedyRule (pruneAlg.run G (initSt x) 3) 0 v = .active
  · have hd := greedy_decided (pruneRun_id G x) h0
    rw [greedy_start_active] at hd
    have hr : v ∈ remainder G (pruneSet G x) := by
      rw [← greedy_start_active]; exact h0
    have hle := comp_card_le_eta G x hr
    rw [status_le_of_ne (by omega) hd]
    exact hd
  · rw [status_le_of_ne (Nat.zero_le s) h0]; exact h0

/-- **Section 5**: the MIS algorithm with predictions is correct: after `η + 3` rounds (and at any
later time) the nodes that output 1 form a maximal independent set. Together with
`predAlg_terminates`, the algorithm is `η`-degrading with consistency 3. -/
theorem predAlg_correct {t : ℕ} (ht : eta G x + 3 ≤ t) :
    IsMIS G {v | predStatus G x t v = .inMIS} := by
  obtain ⟨s, rfl⟩ : ∃ s, t = 3 + s := ⟨t - 3, by omega⟩
  simp only [predStatus_add]
  obtain ⟨h1, h2, h3⟩ := greedy_start_inv G x
  refine greedy_isMIS (pruneRun_id G x) h1 h2 h3 fun v => ?_
  rw [← predStatus_add]
  exact predAlg_terminates G x ht v

/-- **Consistency** (Section 3): if the prediction is a maximal independent set, then `η = 0` and
after 3 rounds every node has terminated with output equal to its prediction. -/
theorem predAlg_consistent (hx : IsMIS G {v | x v = true}) :
    eta G x = 0 ∧ ∀ v, predStatus G x 3 v = if x v = true then .inMIS else .outMIS := by
  refine ⟨eta_eq_zero_of_isMIS G x hx, fun v => ?_⟩
  have := predStatus_add G x 0 v
  rw [Nat.add_zero] at this
  rw [this, greedy_start, pruneStatus, (pruneSet_of_isMIS G x hx).2,
    (pruneSet_of_isMIS G x hx).1]
  simp

omit [Fintype V] in
/-- The MIS algorithm with predictions is a LOCAL algorithm: the state of a node after `t` rounds
only depends on its radius-`t` view (CSLib's `run_isLocal`). -/
theorem predAlg_isLocal (t : ℕ) :
    Cslib.Local.IsLocal t (fun G (c₀ : V → St V) v => (predAlg : Algorithm (St V)).run G c₀ t v) :=
  Algorithm.run_isLocal _ t

/-! ### The Distributed Greedy MIS Algorithm without predictions -/

omit [LinearOrder V] [Fintype V] in
lemma allActive_id [LinearOrder V] (v : V) : (allActive v).id = v := rfl

/-- **Section 4**: the Distributed Greedy MIS Algorithm has round complexity at most `n` on a graph
with `n` nodes (more precisely, at most the maximum size of a connected component), and its output
is an MIS. -/
theorem greedy_round_complexity {t : ℕ} (ht : Fintype.card V ≤ t) :
    (∀ v, status G greedyRule allActive t v ≠ .active) ∧
    IsMIS G {v | status G greedyRule allActive t v = .inMIS} := by
  have hall : ∀ v, status G greedyRule allActive t v ≠ .active := by
    intro v
    have h0 : status G greedyRule (allActive (V := V)) 0 v = .active := rfl
    have hd := greedy_decided (allActive_id) h0
    have hle : (comp G {y | status G greedyRule (allActive (V := V)) 0 y = .active} v).card ≤ t :=
      (Finset.card_le_univ _).trans ht
    rw [status_le_of_ne hle hd]
    exact hd
  refine ⟨hall, greedy_isMIS allActive_id (fun _ _ _ h => by cases h) (fun _ h => by cases h)
    (fun _ _ _ _ h => by cases h) hall⟩

end Podc.GraphAlgorithmsPredictions
