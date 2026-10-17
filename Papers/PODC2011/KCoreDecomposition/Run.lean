import Papers.PODC2011.KCoreDecomposition.Algorithm

/-!
# Synchronous runs of Algorithm 1 and the time / message bounds (§4.2, §4.3)

The synchronous model of §4.2: "during one round, each node receives all messages addressed to it in
the previous round (if any), computes a new coreness estimate and broadcasts a message to all its
neighbors if the estimate has changed with respect to the previous round. At round 1, each node
broadcasts its current estimate (equal to its degree) to all its neighbors." No optimizations.

`run G order n` is the configuration at the end of round `n + 1`: the node states and the set of
nodes that broadcast in round `n + 1`. In each round a node processes the messages it received with
the handler `receive` of Algorithm 1, **in an arbitrary order** given by `order` (any list
enumerating its neighbours; duplicates allowed). The results hold for every such order.

* `run_spec` — the run produces exactly the trajectory `traj` of `Trajectory.lean`;
* `execTime` — the paper's execution time: the number of rounds in which at least one node
  broadcasts; `execTime_eq` — `execTime = stab + 1` (for a nonempty graph);
* `theorem_2`, `theorem_3` — safety and liveness of the synchronous run;
* `theorem_4` — `execTime ≤ 1 + Σ_u (d(u) − k(u))`;
* `theorem_5` — `execTime ≤ N`; `corollary_1` — `execTime ≤ N − K + 1`;
* `corollary_2_updates` — the update messages (rounds `≥ 2`) number at most `Σ_v d(v)² − 2M`;
  `corollary_2_false` — counting also the initial broadcast of round 1 (which Algorithm 1
  performs), the bound fails already for a single edge; `total_messages_le` — `Σ_v d(v)²` bounds all
  messages.
-/

open Finset

set_option linter.unusedSectionVars false

namespace KCoreDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Configuration at the end of a round: node states, and which nodes broadcast in that round. -/
structure Config (V : Type*) where
  /-- local states -/
  st : V → NodeState V
  /-- `sent v`: node `v` broadcast `⟨v, core⟩` to all neighbours in this round -/
  sent : V → Bool

/-- The messages a node receives in the next round, listed in the order `ord`: one message
`⟨v, core_v⟩` from every `v ∈ ord` that broadcast. -/
def inbox (c : Config V) (ord : List V) : List (V × ℕ) :=
  (ord.filter fun v => c.sent v).map fun v => (v, (c.st v).core)

/-- Node `u` after processing its inbox with the handler of Algorithm 1. -/
noncomputable def afterReceive (c : Config V) (ord : List V) (u : V) : NodeState V :=
  (inbox c ord).foldl (receive G u) (c.st u)

/-- `order n u` is an admissible processing order for node `u` in round `n + 2`: it lists exactly
the neighbours of `u` (possibly with repetitions). -/
def IsOrder (order : ℕ → V → List V) : Prop := ∀ n u v, v ∈ order n u ↔ G.Adj u v

/-- The synchronous run: `run G order n` is the configuration at the end of round `n + 1`.
Round 1: initialization and broadcast of the degrees. Round `n + 2`: receive the messages of round
`n + 1`, then (periodic part of Algorithm 1) broadcast iff `changed`, and reset `changed`. -/
noncomputable def run (order : ℕ → V → List V) : ℕ → Config V
  | 0 => ⟨initState G, fun _ => true⟩
  | n + 1 =>
    ⟨fun u => { afterReceive G (run order n) (order n u) u with changed := false },
     fun u => (afterReceive G (run order n) (order n u) u).changed⟩

/-- The paper's execution time: the number of rounds during which at least one node broadcasts. -/
noncomputable def execTime (order : ℕ → V → List V) : ℕ :=
  Set.ncard {n : ℕ | ∃ u, (run G order n).sent u = true}

variable {G}

/-- The run follows the trajectory: at the end of round `n + 1` the estimate of `u` is
`traj G n u`, `u` broadcast in round `n + 1` iff `n = 0` or its estimate just decreased, and `u`
knows the estimates `traj G (n - 1)` of its neighbours (`⊤` in round 1). -/
theorem run_spec {order : ℕ → V → List V} (ho : IsOrder G order) (n : ℕ) (u : V) :
    ((run G order n).st u).core = traj G n u ∧
    ((run G order n).st u).changed = false ∧
    ((run G order n).sent u = true ↔ n = 0 ∨ traj G n u < traj G (n - 1) u) ∧
    (∀ v, G.Adj u v → ((run G order n).st u).est v = if n = 0 then ⊤ else (traj G (n - 1) v : ℕ∞)) := by
  induction n generalizing u with
  | zero => simp [run, initState]
  | succ n ih =>
    set c := run G order n with hc
    -- the inbox of `u`
    set l := inbox c (order n u) with hl
    have hlval : ∀ m ∈ l, m.2 = traj G n m.1 := by
      intro m hm
      simp only [hl, inbox, List.mem_map, List.mem_filter] at hm
      obtain ⟨v, -, rfl⟩ := hm
      exact (ih v).1
    have hlmem : ∀ v, G.Adj u v → ((∃ m ∈ l, m.1 = v) ↔ c.sent v = true) := by
      intro v hv
      simp only [hl, inbox, List.mem_map, List.mem_filter]
      constructor
      · rintro ⟨_, ⟨w, ⟨_, hw⟩, rfl⟩, rfl⟩; exact hw
      · intro hs; exact ⟨_, ⟨v, ⟨(ho n u v).2 hv, hs⟩, rfl⟩, rfl⟩
    obtain ⟨hcore, hch, hsent, hest⟩ := ih u
    obtain ⟨hf1, hf2, hf3, hf4⟩ := foldl_receive (G := G) u l (c.st u)
    -- the new estimates of the neighbours
    have hest' : ∀ v, G.Adj u v → (l.foldl (receive G u) (c.st u)).est v = (traj G n v : ℕ∞) := by
      intro v hv
      rw [foldl_receive_est u l (traj G n) hlval, hest v hv]
      by_cases hs : c.sent v = true
      · rw [ite_eq_left_of_eq_true _ _ (eq_true ((hlmem v hv).2 hs))]
        split_ifs with h0
        · simp
        · exact min_eq_right (by exact_mod_cast traj_anti v (Nat.sub_le n 1))
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt (hlmem v hv).1 hs))]
        have := (ih v).2.2.1
        have hn : n ≠ 0 := fun h0 => hs (this.2 (Or.inl h0))
        rw [ite_eq_right_of_eq_false _ _ (eq_false hn)]
        have hnlt : ¬ traj G n v < traj G (n - 1) v := fun h => hs (this.2 (Or.inr h))
        have hle := traj_anti (G := G) v (Nat.sub_le n 1)
        have : traj G n v = traj G (n - 1) v := by simp only at hle; omega
        rw [this]
    -- the new core
    have hcore' : (l.foldl (receive G u) (c.st u)).core = traj G (n + 1) u := by
      rcases hf3 with heq | heq
      · rw [heq, hcore]
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0
          have hdeg : G.degree u = 0 := by
            by_contra hd
            obtain ⟨v, hv⟩ := G.degree_pos_iff_exists_adj u |>.1 (Nat.pos_of_ne_zero hd)
            have h1 := hest' v hv
            rw [heq, hest v hv] at h1
            simp at h1
          have := traj_succ_le (G := G) 0 u
          simp only [traj_zero] at this hcore ⊢
          omega
        · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hpos
          simp only [zero_add]
          have hsame : ∀ v, G.Adj u v → (traj G (m + 1) v : ℕ∞) = traj G m v := by
            intro v hv
            have h1 := hest' v hv
            rw [heq, hest v hv] at h1
            simpa using h1.symm
          rw [traj_succ_apply (m + 1), computeIndex_congr hsame, traj_succ_apply m,
            computeIndex_idem]
      · rw [heq, hcore, traj_succ_apply]
        exact computeIndex_congr (fun v hv => hest' v hv) _
    refine ⟨hcore', rfl, ?_, ?_⟩
    · change (l.foldl (receive G u) (c.st u)).changed = true ↔ _
      rw [hf4, hcore', hcore, hch]
      simp
    · intro v hv
      simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false, ite_false]
      exact hest' v hv

/-- **Theorem 2 (Safety)** for the synchronous run: estimates are always at least the coreness. -/
theorem theorem_2 {order : ℕ → V → List V} (ho : IsOrder G order) (n : ℕ) (u : V) :
    coreness G u ≤ ((run G order n).st u).core := by
  rw [(run_spec ho n u).1]; exact coreness_le_traj n u

/-- Estimates never increase. -/
theorem core_succ_le {order : ℕ → V → List V} (ho : IsOrder G order) (n : ℕ) (u : V) :
    ((run G order (n + 1)).st u).core ≤ ((run G order n).st u).core := by
  rw [(run_spec ho n u).1, (run_spec ho (n + 1) u).1]; exact traj_succ_le n u

/-- **Theorem 3 (Liveness)** for the synchronous run: from the end of round `stab G + 1` on, every
estimate equals the coreness, and no node broadcasts any more. -/
theorem theorem_3 {order : ℕ → V → List V} (ho : IsOrder G order) :
    ∃ T, ∀ n ≥ T, ∀ u, ((run G order n).st u).core = coreness G u ∧
      (run G order (n + 1)).sent u = false := by
  refine ⟨stab G, fun n hn u => ⟨?_, ?_⟩⟩
  · rw [(run_spec ho n u).1, traj_eq_coreness_of_le hn]
  · have h := (run_spec ho (n + 1) u).2.2.1
    rw [Nat.add_sub_cancel, traj_succ_eq_of_le hn] at h
    simpa using h

/-- The rounds with a broadcast are exactly rounds `1, …, stab G + 1`. -/
theorem exists_sent_iff {order : ℕ → V → List V} (ho : IsOrder G order) [Nonempty V] (n : ℕ) :
    (∃ u, (run G order n).sent u = true) ↔ n ≤ stab G := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp only [zero_le, iff_true]
    obtain ⟨u⟩ := ‹Nonempty V›
    exact ⟨u, (run_spec ho 0 u).2.2.1.2 (Or.inl rfl)⟩
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hpos
    simp only [zero_add]
    have : (∃ u, (run G order (m + 1)).sent u = true) ↔ traj G (m + 1) ≠ traj G m := by
      constructor
      · rintro ⟨u, hu⟩ heq
        have := (run_spec ho (m + 1) u).2.2.1.1 hu
        simp [heq] at this
      · intro hne
        obtain ⟨u, hu⟩ := Function.ne_iff.1 hne
        refine ⟨u, (run_spec ho (m + 1) u).2.2.1.2 (Or.inr ?_)⟩
        have := traj_succ_le (G := G) m u
        simp only [Nat.add_sub_cancel]; omega
    rw [this, traj_succ_ne_iff]; omega

/-- The execution time is `stab G + 1`: one initial round plus one round per update step. -/
theorem execTime_eq {order : ℕ → V → List V} (ho : IsOrder G order) [Nonempty V] :
    execTime G order = stab G + 1 := by
  have : {n : ℕ | ∃ u, (run G order n).sent u = true} = ↑(range (stab G + 1)) := by
    ext n; simp only [Set.mem_ofPred_eq, coe_range, Set.mem_Iio, exists_sent_iff ho]; omega
  rw [execTime, this, Set.ncard_coe_finset, card_range]

theorem execTime_of_isEmpty {order : ℕ → V → List V} [IsEmpty V] : execTime G order = 0 := by
  simp [execTime]

/-- **Theorem 4.** The execution time is at most `1 + Σ_u (d(u) − k(u))`. -/
theorem theorem_4 {order : ℕ → V → List V} (ho : IsOrder G order) :
    execTime G order ≤ 1 + ∑ u, (G.degree u - coreness G u) := by
  cases isEmpty_or_nonempty V
  · rw [execTime_of_isEmpty]; omega
  · rw [execTime_eq ho]; have := stab_le_sum (G := G); omega

/-- **Corollary 1.** With `K` the number of nodes of minimum degree, the execution time is at most
`N − K + 1`. -/
theorem corollary_1 {order : ℕ → V → List V} (ho : IsOrder G order) :
    execTime G order ≤ Fintype.card V - numMinDegree G + 1 := by
  cases isEmpty_or_nonempty V
  · rw [execTime_of_isEmpty]; omega
  · rw [execTime_eq ho]; have := stab_le_card_sub_minDegree (G := G); omega

/-- A slightly stronger form: `N − |{u : d(u) = k(u)}| + 1`. -/
theorem execTime_le_card_sub_correct {order : ℕ → V → List V} (ho : IsOrder G order) :
    execTime G order ≤ Fintype.card V - #(correctSet G 0) + 1 := by
  cases isEmpty_or_nonempty V
  · rw [execTime_of_isEmpty]; omega
  · rw [execTime_eq ho]; have := stab_le_card_sub (G := G); omega

/-- **Theorem 5.** The execution time is at most `N`. -/
theorem theorem_5 {order : ℕ → V → List V} (ho : IsOrder G order) :
    execTime G order ≤ Fintype.card V := by
  cases isEmpty_or_nonempty V
  · rw [execTime_of_isEmpty]; omega
  · have h1 := corollary_1 ho
    have h2 := one_le_numMinDegree (G := G)
    have h3 : numMinDegree G ≤ Fintype.card V := card_le_univ _
    omega

/-! ### Message complexity (§4.3) -/

variable (G) in
/-- Number of messages sent in round `n + 1` (a broadcast of `u` is `d(u)` point-to-point
messages). -/
noncomputable def msgsInRound (order : ℕ → V → List V) (n : ℕ) : ℕ :=
  ∑ u, if (run G order n).sent u = true then G.degree u else 0

/-- Number of strict decreases of an antitone sequence. -/
theorem card_decreases_add_le (f : ℕ → ℕ) (hf : Antitone f) (R : ℕ) :
    #{n ∈ Ico 1 (R + 1) | f n < f (n - 1)} + f R ≤ f 0 := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [show Ico 1 (R + 1 + 1) = insert (R + 1) (Ico 1 (R + 1)) by
      rw [Nat.Ico_succ_right_eq_insert_Ico (by omega)], filter_insert]
    have hle : f (R + 1) ≤ f R := hf (Nat.le_succ R)
    simp only [Nat.add_sub_cancel]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp)]; omega
    · omega

/-- Per node, the number of update broadcasts is at most `d(u) − k(u)`. -/
theorem card_sent_le {order : ℕ → V → List V} (ho : IsOrder G order) (u : V) (R : ℕ) :
    #{n ∈ Ico 1 R | (run G order n).sent u = true} ≤ G.degree u - coreness G u := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp
  obtain ⟨R, rfl⟩ := Nat.exists_eq_add_of_lt hR
  simp only [zero_add]
  have h := card_decreases_add_le (fun n => traj G n u) (traj_anti u) R
  have hk := coreness_le_traj (G := G) R u
  have hsub : {n ∈ Ico 1 (R + 1) | (run G order n).sent u = true} =
      {n ∈ Ico 1 (R + 1) | traj G n u < traj G (n - 1) u} := by
    refine filter_congr fun n hn => ?_
    rw [(run_spec ho n u).2.2.1]
    have : n ≠ 0 := by simp at hn; omega
    simp [this]
  rw [hsub]
  simp only [traj_zero] at h
  omega

/-- **Corollary 2 (update messages).** The messages sent in rounds `2, 3, …` (the update messages)
number at most `Σ_v d(v)² − 2M`. -/
theorem corollary_2_updates {order : ℕ → V → List V} (ho : IsOrder G order) (R : ℕ) :
    ∑ n ∈ Ico 1 R, msgsInRound G order n ≤ ∑ v, G.degree v ^ 2 - 2 * #G.edgeFinset := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  have key : ∑ n ∈ Ico 1 R, msgsInRound G order n =
      ∑ u, G.degree u * #{n ∈ Ico 1 R | (run G order n).sent u = true} := by
    simp only [msgsInRound]
    rw [sum_comm]
    refine sum_congr rfl fun u _ => ?_
    rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
  rw [key]
  have hle : ∀ u, G.degree u * #{n ∈ Ico 1 R | (run G order n).sent u = true} ≤
      G.degree u ^ 2 - G.degree u := by
    intro u
    have h1 := card_sent_le ho u R
    rcases Nat.eq_zero_or_pos (G.degree u) with h0 | hpos
    · simp [h0]
    · obtain ⟨v, hv⟩ := G.degree_pos_iff_exists_adj u |>.1 hpos
      have hk := one_le_coreness_of_adj (G := G) hv
      calc G.degree u * #{n ∈ Ico 1 R | (run G order n).sent u = true}
          ≤ G.degree u * (G.degree u - 1) := Nat.mul_le_mul_left _ (by omega)
        _ = G.degree u ^ 2 - G.degree u := by
          rw [Nat.mul_sub, mul_one, sq]
  calc ∑ u, G.degree u * #{n ∈ Ico 1 R | (run G order n).sent u = true}
      ≤ ∑ u, (G.degree u ^ 2 - G.degree u) := sum_le_sum fun u _ => hle u
    _ = ∑ v, G.degree v ^ 2 - ∑ v, G.degree v := by
      rw [sum_tsub_distrib]
      intro u _
      rw [sq]; exact Nat.le_mul_self _

/-- All messages, including the initial broadcast of round 1, number at most `Σ_v d(v)²`. -/
theorem total_messages_le {order : ℕ → V → List V} (ho : IsOrder G order) (R : ℕ) :
    ∑ n ∈ range R, msgsInRound G order n ≤ ∑ v, G.degree v ^ 2 := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp
  have h0 : msgsInRound G order 0 = ∑ v, G.degree v := by
    simp [msgsInRound, run]
  rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le 1) hR, Nat.Ico_succ_singleton,
    sum_singleton, h0]
  have h1 := corollary_2_updates ho R
  rw [← G.sum_degrees_eq_twice_card_edges] at h1
  have h2 : ∑ v, G.degree v ≤ ∑ v, G.degree v ^ 2 :=
    sum_le_sum fun v _ => by rw [sq]; exact Nat.le_mul_self _
  omega

/-- **Corollary 2 is false if the initial broadcast is counted.** For a single edge (`N = 2`,
`M = 1`), `Σ d(v)² − 2M = 0`, but two messages are sent in round 1. -/
theorem corollary_2_false (order : ℕ → Fin 2 → List (Fin 2)) :
    ∑ v, (⊤ : SimpleGraph (Fin 2)).degree v ^ 2 - 2 * #(⊤ : SimpleGraph (Fin 2)).edgeFinset = 0 ∧
    msgsInRound (⊤ : SimpleGraph (Fin 2)) order 0 = 2 := by
  have hdeg : ∀ v, (⊤ : SimpleGraph (Fin 2)).degree v = 1 := fun v => by
    rw [SimpleGraph.complete_graph_degree]; rfl
  refine ⟨?_, ?_⟩
  · rw [← SimpleGraph.sum_degrees_eq_twice_card_edges]; simp [hdeg]
  · simp [msgsInRound, run, hdeg]

end KCoreDecomposition
