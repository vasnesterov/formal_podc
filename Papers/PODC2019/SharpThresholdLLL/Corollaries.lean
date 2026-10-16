import Papers.PODC2019.SharpThresholdLLL.Parallel

/-!
# Corollaries 1.2 and 1.4: colour-class schedules

Both distributed algorithms first compute a colouring, then iterate through the colour classes.
In each phase they fix in parallel the variables owned by the current colour class.
* Corollary 1.2 (rank 2) colours the variables (the edges of the dependency graph, after merging
  parallel variables) so that variables sharing an event get different colours. A phase fixes
  all variables of one colour simultaneously.
* Corollary 1.4 (rank 3) uses a 2-hop colouring of the dependency graph. In a phase, every node
  of the current colour fixes, one by one, the variables it owns, inside its closed
  neighbourhood `N[v]`.

`colourSchedule` builds the schedule from a grouping of the variables, regions of the groups and
a colouring of the groups. `colourSchedule_valid` shows that the schedule is valid when
same-coloured groups have disjoint regions. Then `valid_schedule_correct` gives the
corollaries' correctness. The schedule has exactly `K` phases (`colourSchedule_length`), one per
colour. The round bounds `O(d + log* n)` and `O(d² + log* n)` follow as well, given the cited
colouring algorithms and an `O(1)`-round LOCAL implementation of a phase. Neither is formalized.
-/

open Finset

set_option linter.unusedSectionVars false

namespace SharpThresholdLLL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : ι → Type} [∀ i, Fintype (α i)]
  [∀ i, DecidableEq (α i)] {V : Type} [Fintype V] [DecidableEq V]

namespace Instance

variable (I : Instance ι α V)

/-- The schedule given by a grouping `grp` of the variables, regions `reg` of the groups, and a
colouring `col` of the groups with `K` colours. Phase `k` consists of the groups of colour `k`.
Each group fixes its variables. -/
noncomputable def colourSchedule {γ : Type} [Fintype γ] [DecidableEq γ] (K : ℕ) (grp : ι → γ)
    (reg : γ → Set V) (col : γ → Fin K) : Schedule ι V :=
  (List.finRange K).map fun k =>
    ((univ.filter fun a => col a = k).toList).map fun a =>
      ((univ.filter fun j => grp j = a).toList, reg a)

lemma colourSchedule_length {γ : Type} [Fintype γ] [DecidableEq γ] (K : ℕ) (grp : ι → γ)
    (reg : γ → Set V) (col : γ → Fin K) : (colourSchedule K grp reg col).length = K := by
  simp [colourSchedule]

/-- The colour-class schedule is valid when every variable affects only events in its group's
region and same-coloured groups have disjoint regions. -/
theorem colourSchedule_valid {γ : Type} [Fintype γ] [DecidableEq γ] (K : ℕ) (grp : ι → γ)
    (reg : γ → Set V) (col : γ → Fin K) (hreg : ∀ j, ∀ t ∈ I.evs j, t ∈ reg (grp j))
    (hdisj : ∀ a b, a ≠ b → col a = col b → Disjoint (reg a) (reg b)) :
    I.ValidSchedule (colourSchedule K grp reg col) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro P hP g hg j hj t ht
    simp only [colourSchedule, List.mem_map] at hP
    obtain ⟨k, -, rfl⟩ := hP
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hg
    simp only [mem_toList, mem_filter, mem_univ, true_and] at hj
    rw [← hj]; exact hreg j t ht
  · intro P hP
    simp only [colourSchedule, List.mem_map] at hP
    obtain ⟨k, -, rfl⟩ := hP
    rw [List.pairwise_map]
    apply (nodup_toList _).pairwise_of_forall_ne
    intro a ha b hb hab
    simp only [mem_toList, mem_filter, mem_univ, true_and] at ha hb
    exact hdisj a b hab (ha.trans hb.symm)
  · rw [List.nodup_flatMap]
    constructor
    · intro P hP
      simp only [colourSchedule, List.mem_map] at hP
      obtain ⟨k, -, rfl⟩ := hP
      rw [List.nodup_flatMap]
      constructor
      · intro g hg
        obtain ⟨a, -, rfl⟩ := List.mem_map.1 hg
        exact nodup_toList _
      · rw [List.pairwise_map]
        apply (nodup_toList _).pairwise_of_forall_ne
        intro a _ b _ hab
        simp only [Function.onFun]
        rw [List.disjoint_left]
        intro j hja hjb
        simp only [mem_toList, mem_filter, mem_univ, true_and] at hja hjb
        exact hab (hja.symm.trans hjb)
    · simp only [colourSchedule]
      rw [List.pairwise_map]
      apply (List.nodup_finRange K).pairwise_of_forall_ne
      intro k _ k' _ hkk'
      simp only [Function.onFun]
      rw [List.disjoint_left]
      intro j hj hj'
      simp only [List.mem_flatMap, List.mem_map, mem_toList, mem_filter, mem_univ,
        true_and] at hj hj'
      obtain ⟨_, ⟨a, ha, rfl⟩, hja⟩ := hj
      obtain ⟨_, ⟨b, hb, rfl⟩, hjb⟩ := hj'
      simp only [mem_toList, mem_filter, mem_univ, true_and] at hja hjb
      apply hkk'
      rw [← ha, ← hb, ← hja, ← hjb]
  · intro j
    refine ⟨_, List.mem_map.2 ⟨col (grp j), List.mem_finRange _, rfl⟩, _,
      List.mem_map.2 ⟨grp j, by simp, rfl⟩, by simp⟩

/-- **Corollary 1.2 (correctness core).** Rank `≤ 2`, `Pr[E_v] ≤ p`, `p · 2^d < 1`. Let `c` be a
colouring of the variables with `K` colours in which variables sharing an event get different
colours. (After merging the variables of each edge, this is a proper edge colouring of the
dependency graph.) Consider the `K`-phase algorithm whose phase `k` fixes all variables of
colour `k` simultaneously, each choice computed from the state at the start of the phase. It can
always be executed, and every execution ends with an assignment avoiding all bad events. -/
theorem corollary_1_2_core {p : ℝ} {d K : ℕ} (hrank : ∀ j, (I.evs j).card ≤ 2)
    (hp : ∀ v, I.pr v ≤ p) (hd : ∀ v, (I.dep v).card ≤ d) (hpd : p * 2 ^ d < 1)
    (c : ι → Fin K) (hc : ∀ j j', j ≠ j' → c j = c j' → Disjoint (I.evs j) (I.evs j')) :
    let S := colourSchedule K id (fun j => (I.evs j : Set V)) c
    S.length = K ∧ (∃ Gs s', skeleton Gs = S ∧ I.RunPhases p init Gs s') ∧
      ∀ Gs s', skeleton Gs = S → I.RunPhases p init Gs s' →
        ∃ x : ∀ i, α i, (∀ i, s'.σ i = some (x i)) ∧ ∀ v, ¬ I.bad v x := by
  intro S
  have hval : I.ValidSchedule S :=
    I.colourSchedule_valid K id _ c (fun j t ht => by simpa using ht)
      (fun a b hab hcol => by simpa [Finset.disjoint_coe] using hc a b hab hcol)
  exact ⟨colourSchedule_length _ _ _ _,
    I.valid_schedule_correct (fun j => (hrank j).trans (by norm_num)) hp hd hpd hval⟩

/-- The closed neighbourhood `N[v]` in the dependency graph. -/
def closedNbhd (v : V) : Finset V := insert v (I.dep v)

lemma mem_closedNbhd_of_mem_evs {j : ι} {v t : V} (hv : v ∈ I.evs j) (ht : t ∈ I.evs j) :
    t ∈ I.closedNbhd v := by
  by_cases h : t = v
  · simp [closedNbhd, h]
  · exact mem_insert_of_mem (I.mem_dep_of_mem_evs ht hv h)

/-- A 2-hop colouring makes the closed neighbourhoods of same-coloured nodes disjoint. -/
lemma disjoint_closedNbhd {K : ℕ} (col : V → Fin K)
    (hcol : ∀ u v, u ≠ v → col u = col v →
      ¬ I.depGraph.Adj u v ∧ ∀ w, ¬ (I.depGraph.Adj u w ∧ I.depGraph.Adj w v))
    {u v : V} (huv : u ≠ v) (hc : col u = col v) : Disjoint (I.closedNbhd u) (I.closedNbhd v) := by
  rw [Finset.disjoint_left]
  intro w hwu hwv
  obtain ⟨hadj, hpath⟩ := hcol u v huv hc
  simp only [closedNbhd, mem_insert, mem_dep] at hwu hwv
  rcases hwu with rfl | hwu <;> rcases hwv with rfl | hwv
  · exact huv rfl
  · exact hadj hwv
  · exact hadj hwu.symm
  · exact hpath w ⟨hwu.symm, hwv⟩

/-- **Corollary 1.4 (correctness core).** Rank `≤ 3`, `Pr[E_v] ≤ p`, `p · 2^d < 1`. Let `col` be
a 2-hop colouring of the dependency graph with `K` colours. Let `owner` assign each variable to
one of its events, for example the event of smallest colour. Consider the `K`-phase algorithm in
which, in phase `k`, every node of colour `k` fixes its owned variables one by one. It can always
be executed, and every execution ends with an assignment avoiding all bad events. -/
theorem corollary_1_4_core {p : ℝ} {d K : ℕ} (hrank : ∀ j, (I.evs j).card ≤ 3)
    (hp : ∀ v, I.pr v ≤ p) (hd : ∀ v, (I.dep v).card ≤ d) (hpd : p * 2 ^ d < 1)
    (col : V → Fin K)
    (hcol : ∀ u v, u ≠ v → col u = col v →
      ¬ I.depGraph.Adj u v ∧ ∀ w, ¬ (I.depGraph.Adj u w ∧ I.depGraph.Adj w v))
    (owner : ι → V) (howner : ∀ j, (I.evs j).Nonempty → owner j ∈ I.evs j) :
    let S := colourSchedule K owner (fun v => (I.closedNbhd v : Set V)) col
    S.length = K ∧ (∃ Gs s', skeleton Gs = S ∧ I.RunPhases p init Gs s') ∧
      ∀ Gs s', skeleton Gs = S → I.RunPhases p init Gs s' →
        ∃ x : ∀ i, α i, (∀ i, s'.σ i = some (x i)) ∧ ∀ v, ¬ I.bad v x := by
  intro S
  have hval : I.ValidSchedule S := by
    apply I.colourSchedule_valid K owner _ col
    · intro j t ht
      exact I.mem_closedNbhd_of_mem_evs (howner j ⟨t, ht⟩) ht
    · intro a b hab hc
      have := I.disjoint_closedNbhd col hcol hab hc
      simpa [Finset.disjoint_coe] using this
  exact ⟨colourSchedule_length _ _ _ _, I.valid_schedule_correct hrank hp hd hpd hval⟩

end Instance

end SharpThresholdLLL
