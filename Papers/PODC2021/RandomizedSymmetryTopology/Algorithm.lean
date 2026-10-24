import Papers.PODC2021.RandomizedSymmetryTopology.MessagePassing

/-!
# From per-facet solvability to a uniform algorithm

Fraigniaud, Gelles, Lotker, PODC 2021, the observation after Definition 3.1.

Definition 3.1 lets the decision map depend on the facet (global state). The paper justifies this
by an algorithm: one round later every party knows the global state up to a permutation of the
names, and can apply a decision map chosen as a function of that (symmetric) information.
We make this precise for leader election in both models:

* a *uniform* algorithm is a family `dec t : Know t → Bool` (party `i` outputs `dec t (Kᵢ(t))` at
  time `t`); `probAlg M dec t` is the probability that its outputs at time `t` elect exactly one
  leader;
* `probAlg_le_probSolves`: no algorithm does better than per-facet solvability;
* `exists_algorithm`: if every party sees, one round later, the multiset of all knowledge values
  (`HasView`, true in both models), a single algorithm achieves `probAlg (t + 1) ≥ probSolves t`;
* `eventuallySolvable_iff_exists_algorithm`: eventual solvability (Definition 3.3) is equivalent to
  the existence of one uniform algorithm whose success probability tends to `1`.
-/

open Finset Filter Topology

namespace Podc.RandomizedSymmetryTopology

variable {n k : ℕ}

/-- Success probability at time `t` of the uniform leader-election algorithm `dec`. -/
noncomputable def probAlg (M : FullInfoModel n k) (dec : (t : ℕ) → M.Know t → Bool) (t : ℕ) : ℝ :=
  probEvent (fun ω t => (fun i => dec t (M.K ω t i)) ∈ leaderElection n) t

/-- No uniform algorithm beats per-facet solvability. -/
theorem probAlg_le_probSolves (M : FullInfoModel n k) (dec : (t : ℕ) → M.Know t → Bool) (t : ℕ) :
    probAlg M dec t ≤ probSolves M (leaderElection n) t := by
  classical
  unfold probAlg probEvent probSolves
  gcongr
  exact fun h => ⟨dec t, h⟩

/-- One round later, every party knows the multiset of all knowledge values. -/
def HasView (M : FullInfoModel n k) : Prop :=
  ∀ t, ∃ v : M.Know (t + 1) → Multiset (M.Know t), ∀ ω i, v (M.K ω (t + 1) i) = univ.val.map (M.K ω t)

/-- The leader-election rule on a multiset of knowledge values: elect yourself iff your value is
the (canonically chosen) value of multiplicity one. -/
noncomputable def leDecide {κ : Type*} (m : Multiset κ) (own : κ) : Bool := by
  classical
  exact if h : ∃ x ∈ m, m.count x = 1 then decide (own = h.choose) else false

theorem leDecide_unique {κ : Type*} (v : Fin n → κ) (hv : ∃ i, ∀ j, j ≠ i → v j ≠ v i) :
    ∃! i, leDecide (univ.val.map v) (v i) = true := by
  classical
  have hcount : ∀ x, (univ.val.map v).count x = (univ.filter fun j => v j = x).card := by
    intro x
    rw [Multiset.count_map, Finset.card, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr fun j _ => eq_comm
  obtain ⟨i, hi⟩ := hv
  have hex : ∃ x ∈ univ.val.map v, (univ.val.map v).count x = 1 := by
    refine ⟨v i, Multiset.mem_map_of_mem _ (mem_univ i), ?_⟩
    rw [hcount, card_eq_one]
    refine ⟨i, ?_⟩
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun h => by_contra fun hne => hi j hne h, fun h => h ▸ rfl⟩
  have hc := hex.choose_spec
  rw [hcount, card_eq_one] at hc
  obtain ⟨l, hl⟩ := hc.2
  have hl' : ∀ j, v j = hex.choose ↔ j = l := fun j => by
    have := congrArg (j ∈ ·) hl
    simpa using this
  refine ⟨l, ?_, fun j hj => ?_⟩
  · simp only [leDecide, hex, ↓reduceDIte, decide_eq_true_eq]; exact (hl' l).2 rfl
  · simp only [leDecide, hex, ↓reduceDIte, decide_eq_true_eq] at hj; exact (hl' j).1 hj

/-- **The observation after Definition 3.1** (for leader election): a single uniform algorithm,
deciding at time `t + 1`, succeeds whenever the global state at time `t` solves leader election. -/
theorem exists_algorithm (M : FullInfoModel n k) (hM : HasView M) :
    ∃ dec : (t : ℕ) → M.Know t → Bool, ∀ t,
      (∀ ω, Solves (leaderElection n) (M.K ω t) →
        (fun i => dec (t + 1) (M.K ω (t + 1) i)) ∈ leaderElection n) ∧
      probSolves M (leaderElection n) t ≤ probAlg M dec (t + 1) := by
  choose v hv using hM
  choose g hg using M.prev
  let dec : (t : ℕ) → M.Know t → Bool := fun t => match t with
    | 0 => fun _ => false
    | t + 1 => fun x => leDecide (v t x) (g t x)
  have hsucc : ∀ ω t, Solves (leaderElection n) (M.K ω t) →
      (fun i => dec (t + 1) (M.K ω (t + 1) i)) ∈ leaderElection n := by
    intro ω t h
    have := leDecide_unique (M.K ω t) ((solves_leaderElection_iff _).1 h)
    show ∃! i, leDecide (v t (M.K ω (t + 1) i)) (g t (M.K ω (t + 1) i)) = true
    simpa only [hv, ← hg] using this
  refine ⟨dec, fun t => ⟨fun ω => hsucc ω t, ?_⟩⟩
  rw [probSolves_eq]
  exact IsGoodEvent.probEvent_le_succ_of (fun ω ω' h => (isGoodEvent_solves M _).isLocal ω ω' t h)
    fun ω h => hsucc ω t h

/-- Definition 3.3 is algorithmically meaningful: leader election is eventually solvable iff one
uniform algorithm succeeds with probability tending to `1`. -/
theorem eventuallySolvable_iff_exists_algorithm (M : FullInfoModel n k) (hM : HasView M) :
    EventuallySolvable M (leaderElection n) ↔
      ∃ dec : (t : ℕ) → M.Know t → Bool, Tendsto (probAlg M dec) atTop (𝓝 1) := by
  constructor
  · intro h
    obtain ⟨dec, hdec⟩ := exists_algorithm M hM
    refine ⟨dec, ?_⟩
    have h1 : Tendsto (fun t => probAlg M dec (t + 1)) atTop (𝓝 1) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le h tendsto_const_nhds (fun t => (hdec t).2)
        fun t => by unfold probAlg; exact IsGoodEvent.probEvent_le_one _
    exact (tendsto_add_atTop_iff_nat 1).1 h1
  · rintro ⟨dec, h⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h tendsto_const_nhds
      (probAlg_le_probSolves M dec) fun t => by rw [probSolves_eq]; exact IsGoodEvent.probEvent_le_one t

/-! ### Both models have views -/

theorem map_univ_eq_cons {β γ : Type*} [Fintype β] [DecidableEq β] (f : β → γ) (i : β) :
    univ.val.map f = f i ::ₘ (univ.erase i).val.map f := by
  rw [← Multiset.map_cons, ← Finset.insert_val_of_notMem (Finset.notMem_erase i univ),
    Finset.insert_erase (mem_univ i)]

theorem hasView_bb (α : Fin n → Fin k) : HasView (bbModel α) := fun t =>
  ⟨fun x => (show BBKnow t × Bool × Multiset (BBKnow t) from x).1 ::ₘ
      (show BBKnow t × Bool × Multiset (BBKnow t) from x).2.2,
    fun ω i => (map_univ_eq_cons (bbK α ω t) i).symm⟩

theorem hasView_mp (α : Fin n → Fin k) (π : PortNumbering n) : HasView (mpModel α π) := by
  classical
  intro t
  refine ⟨fun x => (show MPKnow (n - 1) t × Bool × (Fin (n - 1) → MPKnow (n - 1) t) from x).1 ::ₘ
      univ.val.map (show MPKnow (n - 1) t × Bool × (Fin (n - 1) → MPKnow (n - 1) t) from x).2.2,
    fun ω i => ?_⟩
  show mpK α π ω t i ::ₘ univ.val.map (fun p => mpK α π ω t (π i p)) = univ.val.map (mpK α π ω t)
  rw [map_univ_eq_cons (mpK α π ω t) i]
  congr 1
  have hset : (univ : Finset (Fin (n - 1))).map
      ((π i).toEmbedding.trans (Function.Embedding.subtype _)) = univ.erase i := by
    ext x
    simp only [Finset.mem_map, mem_univ, true_and, Function.Embedding.trans_apply,
      Equiv.coe_toEmbedding, Function.Embedding.coe_subtype, mem_erase, and_true]
    exact ⟨fun ⟨p, hp⟩ => hp ▸ (π i p).2, fun hx => ⟨(π i).symm ⟨x, hx⟩, by simp⟩⟩
  rw [← hset, Finset.map_val, Multiset.map_map]
  rfl

/-- Theorem 4.1 with a uniform algorithm (blackboard model). -/
theorem theorem_4_1_algorithm (α : Fin n → Fin k) :
    (∃ dec, Tendsto (probAlg (bbModel α) dec) atTop (𝓝 1)) ↔ ∃ j, load α j = 1 := by
  rw [← eventuallySolvable_iff_exists_algorithm _ (hasView_bb α), theorem_4_1]

/-- The correct worst-case characterization in the message-passing model of Eq. (2), with uniform
algorithms. -/
theorem worstCase_algorithm_iff (α : Fin n → Fin k) :
    (∀ π : PortNumbering n, ∃ dec, Tendsto (probAlg (mpModel α π) dec) atTop (𝓝 1)) ↔
      ∃ j, load α j = 1 := by
  rw [← worstCase_iff]
  exact forall_congr' fun π => (eventuallySolvable_iff_exists_algorithm _ (hasView_mp α π)).symm

end Podc.RandomizedSymmetryTopology
