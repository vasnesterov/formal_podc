import Papers.PODC2023.LeaderTradeoffs.Tradeoff

/-!
# The `Ω(n log n)` message lower bound for single-send algorithms (Lemmas 3.13, 3.14)

A *single-send* algorithm sends at most one message per node and round. Let `n = m + 1 = 2^k`
and let `A` be a single-send algorithm that elects a leader within `T` rounds for all ID
assignments from `U`, where `|U| ≥ n log₂ n + n T^(log₂ n - 1)` (Lemma 3.14's assumption).

Level `i` of the construction (Lemma 3.14) consists of many pairwise disjoint `2^i`-sets of IDs,
each with a partial port mapping under which it runs in isolation up to a common round `R_i`,
with *capacity* `2^(i-1) - 1` (every node still has that many unlinked nodes in its set) and at
least `M_i` messages sent so far.

* `absorb`: a set `X` of `2^i ≤ n/2` IDs from the pruned universe cannot run in isolation until
  round `T` (repaired Corollary 3.7), so the adversary connects the newly opened ports of `X`
  inside `X` as long as the capacity allows; the first round `ρ` in which this is impossible comes
  after at least `capacity + 1` further messages.
* `merge`: two sets that both stop in round `ρ` are joined in round `ρ`: since every node opens
  at most one port per round, the new links form a perfect matching between them, which leaves
  capacity `2^i - 1` for the merged set.
* `level_step`: pigeonhole over the stop round `ρ ∈ [0, T)` and pairing.

`single_send_lower_bound` (Lemma 3.13): some execution sends at least `(n/2) log₂ n` messages.

Compared with the paper: the stop round `r_I` and the merged execution are chosen per set
(the paper's quantification "for every execution prefix" is not needed); the adversary links
each opener to one unlinked node (the paper's "any one-to-one mappings `g`, `h`" may give a node
two new links, which breaks the capacity bound `|D|/2 - 1`); and we also count the messages of
level `0` (two singletons must exchange a message), which gives `(n/2) log₂ n` instead of
`(n/2)(log₂ n - 1)`.
-/

open Classical Finset Function

namespace LeaderTradeoffs

variable {m : ℕ}

/-- Nodes of `X` not yet linked to `u`. -/
noncomputable def nonNbrs (q : PortMap m) (X : Finset ℕ) (u : ℕ) : Finset ℕ :=
  (X.erase u).filter fun v => ∀ j, q u j ≠ some v

/-- Nodes of `X` that send a message over an undefined port in round `r`. -/
noncomputable def openers (A : Algorithm m) (q : PortMap m) (r : ℕ) (X : Finset ℕ) :
    Finset ℕ :=
  X.filter fun u => ∃ j, q u j = none ∧ (A.send (run A q r u) j).isSome

theorem mem_nonNbrs {q : PortMap m} {X : Finset ℕ} {u v : ℕ} :
    v ∈ nonNbrs q X u ↔ v ∈ X ∧ v ≠ u ∧ ∀ j, q u j ≠ some v := by
  simp only [nonNbrs, Finset.mem_filter, Finset.mem_erase]
  tauto

theorem card_openers_le {A : Algorithm m} {q : PortMap m} {r : ℕ} {X : Finset ℕ} :
    (openers A q r X).card ≤ roundMsgs A q r X := by
  calc (openers A q r X).card = ∑ _u ∈ openers A q r X, 1 := by simp
    _ ≤ ∑ u ∈ openers A q r X, sendCount A (run A q r u) := by
        apply Finset.sum_le_sum
        intro u hu
        simp only [openers, Finset.mem_filter] at hu
        obtain ⟨j, -, hj⟩ := hu.2
        exact Finset.card_pos.2 ⟨j, by simp [hj]⟩
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- One round of absorbing: all ports opened in round `r` are linked inside `X`, each opener to
one unlinked node. -/
theorem absorb_round {A : Algorithm m} (hS : ∀ s, sendCount A s ≤ 1) {q : PortMap m}
    {X : Finset ℕ} (hX : X.card ≤ m + 1) (hwf : WF q X) {r : ℕ} (hval : Valid A q r X)
    {b : ℕ} (hcap : ∀ u ∈ X, (openers A q r X).card + b ≤ (nonNbrs q X u).card) :
    ∃ q' : PortMap m, WF q' X ∧ Valid A q' (r + 1) X ∧
      (∀ r' ≤ r, ∀ u ∈ X, run A q' r' u = run A q r' u) ∧
      ∀ u ∈ X, b ≤ (nonNbrs q' X u).card := by
  set O := openers A q r X with hOdef
  have hOX : O ⊆ X := Finset.filter_subset _ _
  have hne : ∀ u ∈ O, ∃ v, v ∈ nonNbrs q X u := by
    intro u hu
    have h1 := hcap u (hOX hu)
    have h2 : 0 < O.card := Finset.card_pos.2 ⟨u, hu⟩
    exact Finset.card_pos.1 (by omega)
  choose! t ht using hne
  let R : ℕ → Finset ℕ := fun u => (if u ∈ O then {t u} else ∅) ∪ O.filter fun w => t w = u
  let N : ℕ → Finset (Fin m) := fun u =>
    (freePorts q u).filter fun j => (A.send (run A q r u) j).isSome
  have htu : ∀ u ∈ O, t u ∈ X ∧ t u ≠ u ∧ ∀ j, q u j ≠ some (t u) :=
    fun u hu => mem_nonNbrs.1 (ht u hu)
  have hmemR : ∀ u v, v ∈ R u ↔ (u ∈ O ∧ v = t u) ∨ (v ∈ O ∧ t v = u) := by
    intro u v
    simp only [R, Finset.mem_union, Finset.mem_filter]
    by_cases hu : u ∈ O <;> simp [hu]
  have hRsub : ∀ u ∈ X, R u ⊆ (X.erase u) \ nbrs q u := by
    intro u hu v hv
    rw [hmemR] at hv
    simp only [Finset.mem_sdiff, Finset.mem_erase]
    rcases hv with ⟨huO, rfl⟩ | ⟨hvO, htv⟩
    · obtain ⟨h1, h2, h3⟩ := htu u huO
      refine ⟨⟨h2, h1⟩, fun h => ?_⟩
      obtain ⟨j, hj⟩ := mem_nbrs.1 h
      exact h3 j hj
    · obtain ⟨h1, h2, h3⟩ := htu v hvO
      rw [htv] at h1 h2 h3
      refine ⟨⟨fun h => h2 h.symm, hOX hvO⟩, fun h => ?_⟩
      obtain ⟨j, hj⟩ := mem_nbrs.1 h
      obtain ⟨i, hi⟩ := hwf.symm u hu j v hj
      exact h3 i hi
  have hRcardO : ∀ u, (R u).card ≤ O.card := by
    intro u
    by_cases hu : u ∈ O
    · have : R u ⊆ insert (t u) (O.erase u) := by
        intro v hv
        rw [hmemR] at hv
        rcases hv with ⟨-, rfl⟩ | ⟨hvO, htv⟩
        · exact Finset.mem_insert_self _ _
        · refine Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨?_, hvO⟩)
          rintro rfl
          exact (htu v hvO).2.1 htv
      calc (R u).card ≤ (insert (t u) (O.erase u)).card := Finset.card_le_card this
        _ ≤ (O.erase u).card + 1 := Finset.card_insert_le _ _
        _ = O.card := by rw [Finset.card_erase_of_mem hu]; have := Finset.card_pos.2 ⟨u, hu⟩; omega
    · apply Finset.card_le_card
      intro v hv
      rw [hmemR] at hv
      rcases hv with ⟨h, -⟩ | ⟨hvO, -⟩
      · exact absurd h hu
      · exact hvO
  obtain ⟨q', hwf', hext, hcases, -, hN⟩ := augment q X hwf R N
    (fun u hu => (hRsub u hu).trans (Finset.sdiff_subset.trans (Finset.erase_subset _ _)))
    (fun u hu h => by
      have := hRsub u hu h
      simp at this)
    (fun u hu v hv j hj => by
      have := hRsub u hu hv
      simp only [Finset.mem_sdiff] at this
      exact this.2 (mem_nbrs.2 ⟨j, hj⟩))
    (fun u hu v hv => by
      rw [hmemR] at hv ⊢
      rcases hv with ⟨huO, rfl⟩ | ⟨hvO, htv⟩
      · exact Or.inr ⟨huO, rfl⟩
      · exact Or.inl ⟨hvO, htv.symm⟩)
    (fun u _ j hj => by
      simp only [N, freePorts, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hj.1)
    (fun u hu => by
      have h1 : (N u).card ≤ 1 := by
        refine le_trans (Finset.card_le_card ?_) (hS (run A q r u))
        intro j hj
        simp only [N, Finset.mem_filter] at hj
        simp [hj.2]
      rcases Nat.eq_zero_or_pos (N u).card with h0 | hpos
      · omega
      · obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
        simp only [N, freePorts, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have huO : u ∈ O := Finset.mem_filter.2 ⟨hu, j, hj.1, hj.2⟩
        have : t u ∈ R u := (hmemR u (t u)).2 (Or.inl ⟨huO, rfl⟩)
        have := Finset.card_pos.2 ⟨_, this⟩
        omega)
    (fun u hu => by
      have h1 := Finset.card_le_card (hRsub u hu)
      rw [Finset.card_sdiff_of_subset (nbrs_subset hwf hu), Finset.card_erase_of_mem hu] at h1
      have h2 := card_nbrs hwf hu
      omega)
  have hrun : ∀ r' ≤ r, ∀ u ∈ X, run A q' r' u = run A q r' u :=
    run_eq_of_extends hwf hwf' hext hval
  refine ⟨q', hwf', ?_, hrun, ?_⟩
  · intro r' hr' u hu j hj
    have hqj : q u j = none := by
      rcases h : q u j with _ | v
      · rfl
      · rw [hext u hu j v h] at hj; cases hj
    rw [hrun r' (by omega) u hu]
    rcases Nat.lt_or_ge r' r with h | h
    · exact hval r' h u hu j hqj
    · have : r' = r := by omega
      subst this
      by_contra hs
      have hjN : j ∈ N u := by
        simp only [N, freePorts, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hqj, Option.ne_none_iff_isSome.1 hs⟩
      have := hN u hu j hjN
      rw [hj] at this
      cases this
  · intro u hu
    have hsub : nonNbrs q X u \ R u ⊆ nonNbrs q' X u := by
      intro v hv
      simp only [Finset.mem_sdiff, mem_nonNbrs] at hv ⊢
      refine ⟨hv.1.1, hv.1.2.1, fun j hj => ?_⟩
      rcases hcases u hu j v hj with h | h
      · exact hv.1.2.2 j h
      · exact hv.2 h
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.le_card_sdiff (R u) (nonNbrs q X u)
    have h3 := hcap u hu
    have h4 := hRcardO u
    omega

/-- **Absorbing phase** (the round `r_I` of Lemma 3.14). If `X` cannot run in isolation until
round `T`, the adversary keeps `X` isolated (using the capacity `c`) until some round `ρ < T` in
which the nodes of `X` have sent at least `c + 1` further messages since round `R`. -/
theorem absorb {A : Algorithm m} (hS : ∀ s, sendCount A s ≤ 1) {T R c M : ℕ}
    {X : Finset ℕ} (hX : X.card ≤ m + 1) (hiso : ¬ Isolable A T X) (hRT : R ≤ T)
    {q : PortMap m} (hwf : WF q X) (hval : Valid A q R X)
    (hcap : ∀ u ∈ X, c ≤ (nonNbrs q X u).card) (hM : M ≤ msgs A q R X) :
    ∃ ρ, R ≤ ρ ∧ ρ < T ∧ ∃ q' : PortMap m, WF q' X ∧ Valid A q' ρ X ∧
      M + c + 1 ≤ msgs A q' (ρ + 1) X := by
  have claim : ∀ d, R + d ≤ T →
      (∃ ρ, R ≤ ρ ∧ ρ < R + d ∧ ∃ q' : PortMap m, WF q' X ∧ Valid A q' ρ X ∧
        M + c + 1 ≤ msgs A q' (ρ + 1) X) ∨
      (∃ (q' : PortMap m) (w : ℕ), WF q' X ∧ Valid A q' (R + d) X ∧ w ≤ c ∧
        M + w ≤ msgs A q' (R + d) X ∧ ∀ u ∈ X, c ≤ (nonNbrs q' X u).card + w) := by
    intro d
    induction d with
    | zero => intro _; exact Or.inr ⟨q, 0, hwf, hval, Nat.zero_le _, by simpa using hM,
        fun u hu => by simpa using hcap u hu⟩
    | succ d ih =>
      intro hd
      rcases ih (by omega) with ⟨ρ, h1, h2, rest⟩ | ⟨q', w, hwf', hval', hw, hM', hcap'⟩
      · exact Or.inl ⟨ρ, h1, by omega, rest⟩
      · set o := (openers A q' (R + d) X).card
        by_cases hco : c + 1 ≤ w + o
        · refine Or.inl ⟨R + d, by omega, by omega, q', hwf', hval', ?_⟩
          rw [msgs_succ]
          have := card_openers_le (A := A) (q := q') (r := R + d) (X := X)
          omega
        · obtain ⟨q'', hwf'', hval'', hrun, hcap''⟩ :=
            absorb_round (b := c - w - o) hS hX hwf' hval'
              (fun u hu => by have := hcap' u hu; omega)
          refine Or.inr ⟨q'', w + o, hwf'', by rw [← add_assoc]; exact hval'', by omega, ?_,
            fun u hu => by have := hcap'' u hu; omega⟩
          rw [show R + (d + 1) = R + d + 1 by omega, msgs_succ]
          have h1 : msgs A q'' (R + d) X = msgs A q' (R + d) X :=
            msgs_congr fun r' hr' u hu => hrun r' hr'.le u hu
          have h2 : roundMsgs A q'' (R + d) X = roundMsgs A q' (R + d) X :=
            roundMsgs_congr fun u hu => hrun _ le_rfl u hu
          have := card_openers_le (A := A) (q := q') (r := R + d) (X := X)
          omega
  rcases claim (T - R) (by omega) with ⟨ρ, h1, h2, rest⟩ | ⟨q', w, hwf', hval', -⟩
  · exact ⟨ρ, h1, by omega, rest⟩
  · exact absurd ⟨q', hwf', by rw [show R + (T - R) = T by omega] at hval'; exact hval'⟩ hiso

/-- **Merging** two sets that stop in the same round `ρ` (Lemma 3.14, inductive step): the ports
opened in round `ρ` (at most one per node) are linked along a perfect matching between the two
sets. -/
theorem merge {A : Algorithm m} (hS : ∀ s, sendCount A s ≤ 1) {X Y : Finset ℕ}
    (hXY : Disjoint X Y) {s : ℕ} (hXc : X.card = s) (hYc : Y.card = s) (hs : s + s ≤ m + 1)
    {qX qY : PortMap m} {ρ : ℕ} (hX : WF qX X) (hvX : Valid A qX ρ X) (hY : WF qY Y)
    (hvY : Valid A qY ρ Y) :
    ∃ q : PortMap m, WF q (X ∪ Y) ∧ Valid A q (ρ + 1) (X ∪ Y) ∧
      msgs A q (ρ + 1) (X ∪ Y) = msgs A qX (ρ + 1) X + msgs A qY (ρ + 1) Y ∧
      ∀ u ∈ X ∪ Y, s - 1 ≤ (nonNbrs q (X ∪ Y) u).card := by
  -- glue the two isolated executions
  let p : PortMap m := fun u => if u ∈ X then qX u else qY u
  have hpX : ∀ u ∈ X, p u = qX u := fun u hu => by simp [p, hu]
  have hpY : ∀ u ∈ Y, p u = qY u := fun u hu => by
    have : u ∉ X := Finset.disjoint_right.1 hXY hu
    simp [p, this]
  have hrunX : ∀ r, ∀ u ∈ X, run A p r u = run A qX r u :=
    run_congr hpX (fun u hu j v h => hX.mem u hu j v (by rw [← hpX u hu]; exact h))
  have hrunY : ∀ r, ∀ u ∈ Y, run A p r u = run A qY r u :=
    run_congr hpY (fun u hu j v h => hY.mem u hu j v (by rw [← hpY u hu]; exact h))
  -- links of `p` stay in the own set
  have hside : ∀ u ∈ X ∪ Y, ∀ j v, p u j = some v → (u ∈ X ↔ v ∈ X) := by
    intro u hu j v h
    rcases Finset.mem_union.1 hu with hu | hu
    · rw [hpX u hu] at h
      exact ⟨fun _ => hX.mem u hu j v h, fun _ => hu⟩
    · rw [hpY u hu] at h
      have hvY := hY.mem u hu j v h
      exact ⟨fun h' => absurd h' (Finset.disjoint_right.1 hXY hu),
        fun h' => absurd h' (Finset.disjoint_right.1 hXY hvY)⟩
  have hwf : WF p (X ∪ Y) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro u hu j v h
      rcases Finset.mem_union.1 hu with hu | hu
      · rw [hpX u hu] at h; exact Finset.mem_union_left _ (hX.mem u hu j v h)
      · rw [hpY u hu] at h; exact Finset.mem_union_right _ (hY.mem u hu j v h)
    · intro u hu j h
      rcases Finset.mem_union.1 hu with hu | hu
      · rw [hpX u hu] at h; exact hX.ne u hu j h
      · rw [hpY u hu] at h; exact hY.ne u hu j h
    · intro u hu i j v hi hj
      rcases Finset.mem_union.1 hu with hu | hu
      · rw [hpX u hu] at hi hj; exact hX.inj u hu i j v hi hj
      · rw [hpY u hu] at hi hj; exact hY.inj u hu i j v hi hj
    · intro u hu j v h
      rcases Finset.mem_union.1 hu with hu | hu
      · rw [hpX u hu] at h
        obtain ⟨i, hi⟩ := hX.symm u hu j v h
        exact ⟨i, by rw [hpX v (hX.mem u hu j v h)]; exact hi⟩
      · rw [hpY u hu] at h
        obtain ⟨i, hi⟩ := hY.symm u hu j v h
        exact ⟨i, by rw [hpY v (hY.mem u hu j v h)]; exact hi⟩
  have hval : Valid A p ρ (X ∪ Y) := by
    intro r' hr' u hu j hj
    rcases Finset.mem_union.1 hu with hu | hu
    · rw [hpX u hu] at hj; rw [hrunX r' u hu]; exact hvX r' hr' u hu j hj
    · rw [hpY u hu] at hj; rw [hrunY r' u hu]; exact hvY r' hr' u hu j hj
  -- the perfect matching
  have hc : Fintype.card X = Fintype.card Y := by simp [hXc, hYc]
  let β : X ≃ Y := Fintype.equivOfCardEq hc
  let partner : ℕ → ℕ := fun u =>
    if h : u ∈ X then (β ⟨u, h⟩).1 else if h' : u ∈ Y then (β.symm ⟨u, h'⟩).1 else u
  have hpartX : ∀ u (h : u ∈ X), partner u = (β ⟨u, h⟩).1 := fun u h => by simp [partner, h]
  have hpartY : ∀ u (h : u ∈ Y), partner u = (β.symm ⟨u, h⟩).1 := fun u h => by
    have : u ∉ X := Finset.disjoint_right.1 hXY h
    simp [partner, this, h]
  have hpart_side : ∀ u ∈ X ∪ Y, partner u ∈ X ∪ Y ∧ (u ∈ X ↔ partner u ∉ X) := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · rw [hpartX u hu]
      exact ⟨Finset.mem_union_right _ (β ⟨u, hu⟩).2,
        ⟨fun _ => Finset.disjoint_right.1 hXY (β ⟨u, hu⟩).2, fun _ => hu⟩⟩
    · rw [hpartY u hu]
      exact ⟨Finset.mem_union_left _ (β.symm ⟨u, hu⟩).2,
        ⟨fun h => absurd h (Finset.disjoint_right.1 hXY hu), fun h => absurd (β.symm ⟨u, hu⟩).2 h⟩⟩
  have hpart_inv : ∀ u ∈ X ∪ Y, partner (partner u) = u := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · rw [hpartX u hu, hpartY _ (β ⟨u, hu⟩).2]
      simp
    · rw [hpartY u hu, hpartX _ (β.symm ⟨u, hu⟩).2]
      simp
  let R : ℕ → Finset ℕ := fun u => {partner u}
  let N : ℕ → Finset (Fin m) := fun u =>
    (freePorts p u).filter fun j => (A.send (run A p ρ u) j).isSome
  obtain ⟨q, hwfq, hext, hcases, -, hN⟩ := augment p (X ∪ Y) hwf R N
    (fun u hu => Finset.singleton_subset_iff.2 (hpart_side u hu).1)
    (fun u hu h => by
      rw [Finset.mem_singleton] at h
      have := (hpart_side u hu).2
      rw [← h] at this
      tauto)
    (fun u hu v hv j hj => by
      rw [Finset.mem_singleton] at hv
      have h1 := hside u hu j v hj
      have h2 := (hpart_side u hu).2
      rw [← hv] at h2
      tauto)
    (fun u hu v hv => by
      rw [Finset.mem_singleton] at hv ⊢
      rw [hv, hpart_inv u hu])
    (fun u _ j hj => by
      simp only [N, freePorts, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hj.1)
    (fun u _ => by
      refine le_trans (Finset.card_le_card ?_) (hS (run A p ρ u))
      intro j hj
      simp only [N, Finset.mem_filter] at hj
      simp [hj.2])
    (fun u hu => by
      simp only [R, Finset.card_singleton]
      have h1 := card_nbrs hwf hu
      have h2 : nbrs p u ⊆ (if u ∈ X then X else Y).erase u := by
        intro v hv
        obtain ⟨j, hj⟩ := mem_nbrs.1 hv
        refine Finset.mem_erase.2 ⟨fun h => hwf.ne u hu j (h ▸ hj), ?_⟩
        rcases Finset.mem_union.1 hu with hu' | hu'
        · rw [if_pos hu']; exact (hside u hu j v hj).1 hu'
        · have : u ∉ X := Finset.disjoint_right.1 hXY hu'
          rw [if_neg this]
          rw [hpY u hu'] at hj
          exact hY.mem u hu' j v hj
      have h3 := Finset.card_le_card h2
      have h4 : u ∈ (if u ∈ X then X else Y) := by
        rcases Finset.mem_union.1 hu with hu' | hu'
        · rw [if_pos hu']; exact hu'
        · rw [if_neg (Finset.disjoint_right.1 hXY hu')]; exact hu'
      have h5 : (if u ∈ X then X else Y).card = s := by split_ifs <;> assumption
      rw [Finset.card_erase_of_mem h4, h5] at h3
      have : 0 < s := by
        rw [← h5]; exact Finset.card_pos.2 ⟨u, h4⟩
      omega)
  have hrun : ∀ r' ≤ ρ, ∀ u ∈ X ∪ Y, run A q r' u = run A p r' u :=
    run_eq_of_extends hwf hwfq hext hval
  refine ⟨q, hwfq, ?_, ?_, ?_⟩
  · intro r' hr' u hu j hj
    have hpj : p u j = none := by
      rcases h : p u j with _ | v
      · rfl
      · rw [hext u hu j v h] at hj; cases hj
    rw [hrun r' (by omega) u hu]
    rcases Nat.lt_or_ge r' ρ with h | h
    · exact hval r' h u hu j hpj
    · have : r' = ρ := by omega
      subst this
      by_contra hs'
      have hjN : j ∈ N u := by
        simp only [N, freePorts, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hpj, Option.ne_none_iff_isSome.1 hs'⟩
      have := hN u hu j hjN
      rw [hj] at this
      cases this
  · rw [msgs_congr (q := p) (fun r' hr' u hu => hrun r' (by omega) u hu), msgs_union hXY,
      msgs_congr (q := qX) (fun r' _ u hu => hrunX r' u hu),
      msgs_congr (q := qY) (fun r' _ u hu => hrunY r' u hu)]
  · intro u hu
    -- the other side, minus the partner, is unlinked
    let Z := if u ∈ X then Y else X
    have hZc : Z.card = s := by simp only [Z]; split_ifs <;> assumption
    have hpZ : partner u ∈ Z := by
      have := hpart_side u hu
      simp only [Z]
      split_ifs with h
      · have h2 := this.2.1 h
        rcases Finset.mem_union.1 this.1 with h3 | h3
        · exact absurd h3 h2
        · exact h3
      · rcases Finset.mem_union.1 this.1 with h3 | h3
        · exact h3
        · exfalso
          have : partner u ∉ X := Finset.disjoint_right.1 hXY h3
          rcases Finset.mem_union.1 hu with h4 | h4
          · exact h h4
          · rw [hpartY u h4] at this
            exact this (β.symm ⟨u, h4⟩).2
    have hsub : Z.erase (partner u) ⊆ nonNbrs q (X ∪ Y) u := by
      intro v hv
      rw [Finset.mem_erase] at hv
      have hvZ := hv.2
      have hside_v : (u ∈ X ↔ v ∉ X) := by
        simp only [Z] at hvZ
        split_ifs at hvZ with h
        · exact ⟨fun _ => Finset.disjoint_right.1 hXY hvZ, fun _ => h⟩
        · refine ⟨fun h' => absurd h' h, fun h' => absurd hvZ h'⟩
      rw [mem_nonNbrs]
      refine ⟨?_, ?_, ?_⟩
      · simp only [Z] at hvZ
        split_ifs at hvZ
        · exact Finset.mem_union_right _ hvZ
        · exact Finset.mem_union_left _ hvZ
      · intro h
        rw [h] at hside_v
        tauto
      · intro j hj
        rcases hcases u hu j v hj with h | h
        · have := hside u hu j v h
          tauto
        · rw [Finset.mem_singleton] at h
          exact hv.1 h
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hpZ, hZc] at this
    exact this

end LeaderTradeoffs
