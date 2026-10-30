import Papers.PODC2025.GraphAlgorithmsPredictions.Algorithm

/-!
# Analysis of the Distributed Greedy MIS Algorithm

Section 4 of Boyar–Ellen–Larsen (PODC 2025 BA), Lemma 1 of the full version: started from any
configuration whose terminated part is an extendable partial solution, the Distributed Greedy MIS
Algorithm terminates every node `v` within `s` rounds, where `s` is the number of nodes of the
component of `v` in the subgraph induced by the active nodes; the nodes that output 1 form an MIS.

* Invariants (`Indep`, `OutDom`, `Clean`): the nodes that output 1 are independent, every node that
  output 0 has a neighbour that output 1, and (before odd rounds) no active node has a neighbour that
  output 1. `greedy_inv`.
* `greedy_decided`: the round bound.
* `greedy_isMIS`: once all nodes have terminated, the output is an MIS.
-/

namespace Podc.GraphAlgorithmsPredictions

open SimpleGraph Cslib.LocallyIterative

variable {V : Type*} [LinearOrder V]

/-! ### Invariants -/

/-- The nodes that output 1 are independent. -/
def Indep (G : SimpleGraph V) (σ : V → Status) : Prop :=
  ∀ u w, G.Adj u w → σ u = .inMIS → σ w ≠ .inMIS

/-- Every node that output 0 has a neighbour that output 1. -/
def OutDom (G : SimpleGraph V) (σ : V → Status) : Prop :=
  ∀ v, σ v = .outMIS → ∃ u, G.Adj v u ∧ σ u = .inMIS

/-- No active node has a neighbour that output 1. -/
def Clean (G : SimpleGraph V) (σ : V → Status) : Prop :=
  ∀ v, σ v = .active → ∀ u, G.Adj v u → σ u ≠ .inMIS

omit [LinearOrder V] in
/-- When all nodes have terminated, the invariants say that the nodes with output 1 form an MIS. -/
lemma isMIS_of_inv {G : SimpleGraph V} {σ : V → Status} (h1 : Indep G σ) (h2 : OutDom G σ)
    (hall : ∀ v, σ v ≠ .active) : IsMIS G {v | σ v = .inMIS} := by
  refine ⟨fun u hu w hw _ hadj => h1 u w hadj hu hw, fun v hv => ?_⟩
  have : σ v = .outMIS := by
    have := hall v
    simp only [Set.mem_ofPred_eq] at hv
    cases h : σ v <;> simp_all
  obtain ⟨u, hadj, hu⟩ := h2 v this
  exact ⟨u, hu, hadj⟩

lemma greedyRule_even {t : ℕ} (ht : Even t) : greedyRule t = .max := by simp [greedyRule, ht]

lemma greedyRule_odd {t : ℕ} (ht : ¬ Even t) : greedyRule t = .out := by simp [greedyRule, ht]

variable {G : SimpleGraph V} {c : V → St V}

/-- Abbreviation: status after `t` rounds of the greedy algorithm. -/
local notation "σ" => status G greedyRule c

section
variable (hc : ∀ v, (c v).id = v)
include hc

lemma max_round_in {t : ℕ} (ht : Even t) {v : V} (hv : σ t v = .active)
    (hmax : ∀ u, G.Adj v u → σ t u = .active → u < v) : σ (t + 1) v = .inMIS := by
  classical
  rw [status_succ_max hc (greedyRule_even ht), ite_eq_left ⟨hv, hmax⟩]

lemma max_round_active {t : ℕ} (ht : Even t) {v u : V} (hv : σ t v = .active) (hadj : G.Adj v u)
    (hu : σ t u = .active) (hlt : v < u) : σ (t + 1) v = .active := by
  classical
  rw [status_succ_max hc (greedyRule_even ht),
    ite_eq_right (fun h => absurd (h.2 u hadj hu) (not_lt.2 hlt.le)), hv]

omit hc in
lemma out_round_out {t : ℕ} (ht : ¬ Even t) {v u : V} (hv : σ t v = .active) (hadj : G.Adj v u)
    (hu : σ t u = .inMIS) : σ (t + 1) v = .outMIS := by
  classical
  rw [status_succ_out (greedyRule_odd ht), ite_eq_left ⟨hv, u, hadj, hu⟩]

/-- The invariants are preserved by the greedy algorithm. -/
theorem greedy_inv (h1 : Indep G (σ 0)) (h2 : OutDom G (σ 0)) (h3 : Clean G (σ 0)) :
    ∀ t, Indep G (σ t) ∧ OutDom G (σ t) ∧ (Even t → Clean G (σ t)) := by
  classical
  intro t
  induction t with
  | zero => exact ⟨h1, h2, fun _ => h3⟩
  | succ t ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    -- terminated nodes keep their status
    have keep : ∀ v, σ t v ≠ .active → σ (t + 1) v = σ t v := fun v h => status_succ_of_ne h
    by_cases ht : Even t
    · have hs := fun v => status_succ_max (G := G) (c := c) hc (greedyRule_even ht) v
      have cl := i3 ht
      refine ⟨fun u w hadj hu hw => ?_, fun v hv => ?_, fun h => absurd h (by
        rw [Nat.even_add_one]; exact not_not.2 ht)⟩
      · rw [hs] at hu hw
        split_ifs at hu hw with hu' hw' hw'
        · exact absurd (hu'.2 w hadj hw'.1) (not_lt.2 (hw'.2 u hadj.symm hu'.1).le)
        · exact cl u hu'.1 w hadj hw
        · exact cl w hw'.1 u hadj.symm hu
        · exact i1 u w hadj hu hw
      · rw [hs] at hv
        split_ifs at hv with hv'
        obtain ⟨u, hadj, hu⟩ := i2 v hv
        exact ⟨u, hadj, by rw [keep u (by rw [hu]; simp), hu]⟩
    · have hs := fun v => status_succ_out (G := G) (c := c) (greedyRule_odd ht) v
      have inn : ∀ u, σ (t + 1) u = .inMIS → σ t u = .inMIS := by
        intro u hu
        rw [hs] at hu
        split_ifs at hu
        exact hu
      refine ⟨fun u w hadj hu hw => i1 u w hadj (inn u hu) (inn w hw), fun v hv => ?_,
        fun _ v hv u hadj hu => ?_⟩
      · rw [hs] at hv
        split_ifs at hv with hv'
        · obtain ⟨u, hadj, hu⟩ := hv'.2
          exact ⟨u, hadj, by rw [keep u (by rw [hu]; simp), hu]⟩
        · obtain ⟨u, hadj, hu⟩ := i2 v hv
          exact ⟨u, hadj, by rw [keep u (by rw [hu]; simp), hu]⟩
      · rw [hs] at hv
        split_ifs at hv with hv'
        exact hv' ⟨hv, u, hadj, inn u hu⟩

/-- Once every node has terminated, the output of the greedy algorithm is an MIS. -/
theorem greedy_isMIS (h1 : Indep G (σ 0)) (h2 : OutDom G (σ 0)) (h3 : Clean G (σ 0)) {t : ℕ}
    (hall : ∀ v, σ t v ≠ .active) : IsMIS G {v | σ t v = .inMIS} := by
  obtain ⟨i1, i2, -⟩ := greedy_inv hc h1 h2 h3 t
  exact isMIS_of_inv i1 i2 hall

end

/-! ### The round bound -/

omit [LinearOrder V] in
lemma restrict_reachable_mem {R : Set V} {a b : V} (h : (restrict G R).Reachable a b)
    (ha : a ∈ R) : b ∈ R := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ha
  | cons hadj _ ih => exact ih hadj.2.2

open Classical in
/-- The active nodes of a set `S` after `t` rounds. -/
private noncomputable def actIn (S : Finset V) (t : ℕ) : Finset V :=
  S.filter fun u => σ t u = .active

private lemma actIn_mono {S : Finset V} {t t' : ℕ} (h : t ≤ t') :
    actIn (G := G) (c := c) S t' ⊆ actIn (G := G) (c := c) S t := by
  classical
  intro u hu
  simp only [actIn, Finset.mem_filter] at hu ⊢
  exact ⟨hu.1, active_of_active_le h hu.2⟩

/-- `S` is closed under adjacency among initially active nodes (e.g. a connected component of the
subgraph induced by the initially active nodes). -/
def Closed (H : SimpleGraph V) (c₀ : V → St V) (S : Finset V) : Prop :=
  ∀ w ∈ S, ∀ u, H.Adj w u → status H greedyRule c₀ 0 w = .active →
    status H greedyRule c₀ 0 u = .active → u ∈ S

/-- Active neighbours of active nodes of a closed set stay in the set. -/
private lemma nbr_mem {S : Finset V} (hS : Closed G c S) {t : ℕ} {w u : V}
    (hw : w ∈ actIn (G := G) (c := c) S t) (hadj : G.Adj w u) (hu : σ t u = .active) :
    u ∈ actIn (G := G) (c := c) S t := by
  classical
  simp only [actIn, Finset.mem_filter] at hw ⊢
  exact ⟨hS w hw.1 u hadj (active_of_active_le (Nat.zero_le t) hw.2)
    (active_of_active_le (Nat.zero_le t) hu), hu⟩

section
variable (hc : ∀ v, (c v).id = v)
include hc

private lemma step_one {S : Finset V} (hS : Closed G c S) {t : ℕ} (ht : Even t)
    (hne : (actIn (G := G) (c := c) S t).Nonempty) :
    actIn (G := G) (c := c) S (t + 1) ⊆
      (actIn (G := G) (c := c) S t).erase ((actIn (G := G) (c := c) S t).max' hne) := by
  classical
  set a := actIn (G := G) (c := c) S t with ha
  set m := a.max' hne
  have hm : m ∈ a := a.max'_mem hne
  have hmact : σ t m = .active := (Finset.mem_filter.1 hm).2
  have hin : σ (t + 1) m = .inMIS := by
    refine max_round_in hc ht hmact fun u hadj hu => ?_
    have hua := nbr_mem hS hm hadj hu
    exact lt_of_le_of_ne (a.le_max' u hua) (G.ne_of_adj hadj).symm
  intro u hu
  refine Finset.mem_erase.2 ⟨fun h => ?_, actIn_mono (Nat.le_succ t) hu⟩
  subst h
  have := (Finset.mem_filter.1 hu).2
  rw [hin] at this
  cases this

private lemma step_two {S : Finset V} (hS : Closed G c S) {t : ℕ} (ht : Even t)
    (h2 : 2 ≤ (actIn (G := G) (c := c) S t).card) :
    (actIn (G := G) (c := c) S (t + 2)).card + 2 ≤ (actIn (G := G) (c := c) S t).card := by
  classical
  set a := actIn (G := G) (c := c) S t with ha
  have hne : a.Nonempty := Finset.card_pos.1 (by omega)
  set m := a.max' hne
  have hm : m ∈ a := a.max'_mem hne
  have hmact : σ t m = .active := (Finset.mem_filter.1 hm).2
  have hin : σ (t + 1) m = .inMIS := by
    refine max_round_in hc ht hmact fun u hadj hu => ?_
    have hua := nbr_mem hS hm hadj hu
    exact lt_of_le_of_ne (a.le_max' u hua) (G.ne_of_adj hadj).symm
  -- it suffices to find a second element of `a` that is terminated after round `t + 2`
  suffices H : ∃ y ∈ a, y ≠ m ∧ σ (t + 2) y ≠ .active by
    obtain ⟨y, hy, hym, hyt⟩ := H
    have hsub : actIn (G := G) (c := c) S (t + 2) ⊆ (a.erase m).erase y := by
      intro u hu
      have hu2 := (Finset.mem_filter.1 hu).2
      refine Finset.mem_erase.2 ⟨fun h => hyt (h ▸ hu2), Finset.mem_erase.2 ⟨fun h => ?_,
        actIn_mono (by omega) hu⟩⟩
      subst h
      rw [status_le_of_ne (show t + 1 ≤ t + 2 by omega) (by rw [hin]; simp), hin] at hu2
      cases hu2
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hym, hy⟩),
      Finset.card_erase_of_mem hm] at this
    omega
  by_cases hnb : ∃ u, G.Adj m u ∧ σ t u = .active
  · obtain ⟨u, hadj, hu⟩ := hnb
    have hua := nbr_mem hS hm hadj hu
    have hlt : u < m := lt_of_le_of_ne (a.le_max' u hua) (G.ne_of_adj hadj).symm
    have hu1 : σ (t + 1) u = .active := max_round_active hc ht hu hadj.symm hmact hlt
    have hu2 : σ (t + 1 + 1) u = .outMIS :=
      out_round_out (by rw [Nat.even_add_one]; exact not_not.2 ht) hu1 hadj.symm hin
    exact ⟨u, hua, (G.ne_of_adj hadj).symm, by rw [hu2]; simp⟩
  · push Not at hnb
    have hne' : (a.erase m).Nonempty := by
      rw [← Finset.card_pos, Finset.card_erase_of_mem hm]; omega
    set m' := (a.erase m).max' hne'
    have hm' : m' ∈ a.erase m := (a.erase m).max'_mem hne'
    have hm'a := Finset.mem_of_mem_erase hm'
    have hm'm := Finset.ne_of_mem_erase hm'
    have hm'act : σ t m' = .active := (Finset.mem_filter.1 hm'a).2
    have hin' : σ (t + 1) m' = .inMIS := by
      refine max_round_in hc ht hm'act fun u hadj hu => ?_
      have hua := nbr_mem hS hm'a hadj hu
      have hum : u ≠ m := by
        rintro rfl
        exact hnb m' hadj.symm hm'act
      exact lt_of_le_of_ne ((a.erase m).le_max' u (Finset.mem_erase.2 ⟨hum, hua⟩))
        (G.ne_of_adj hadj).symm
    refine ⟨m', hm'a, hm'm, ?_⟩
    rw [status_le_of_ne (show t + 1 ≤ t + 2 by omega) (by rw [hin']; simp), hin']
    simp

/-- Round bound for a closed set `S`: every node of `S` has terminated after `|S|` rounds of the
Distributed Greedy MIS Algorithm. -/
theorem greedy_decided_of_closed {S : Finset V} (hS : Closed G c S) {v₀ : V} (hv₀ : v₀ ∈ S) :
    σ S.card v₀ ≠ .active := by
  classical
  let f : ℕ → ℕ := fun j => (actIn (G := G) (c := c) S (2 * j)).card
  have hf : ∀ j, f j = 0 ∨ f j + 2 * j ≤ S.card := by
    intro j
    induction j with
    | zero => exact Or.inr (by simpa [f, actIn] using Finset.card_filter_le S _)
    | succ j ih =>
      have hev : Even (2 * j) := even_two_mul j
      have hmono : f (j + 1) ≤ f j := Finset.card_le_card (actIn_mono (by omega))
      rcases Nat.lt_or_ge (f j) 2 with hlt | hge
      · left
        rcases Nat.lt_succ_iff.1 hlt |>.lt_or_eq with h | h
        · omega
        · have hne : (actIn (G := G) (c := c) S (2 * j)).Nonempty :=
            Finset.card_pos.1 (by simp only [f] at h; omega)
          have hc1 := Finset.card_le_card (step_one hc hS hev hne)
          rw [Finset.card_erase_of_mem (Finset.max'_mem _ _)] at hc1
          have : f (j + 1) ≤ (actIn (G := G) (c := c) S (2 * j + 1)).card :=
            Finset.card_le_card (actIn_mono (by omega))
          simp only [f] at h this ⊢
          omega
      · right
        have := step_two hc hS hev hge
        rw [show 2 * j + 2 = 2 * (j + 1) by ring] at this
        rcases ih with h | h
        · omega
        · simp only [f] at h this ⊢; omega
  have notin : ∀ t, v₀ ∉ actIn (G := G) (c := c) S t → σ t v₀ ≠ .active := by
    intro t h ht
    exact h (Finset.mem_filter.2 ⟨hv₀, ht⟩)
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' S.card
  · rw [hj]
    refine notin _ fun h => ?_
    have h0 : f j ≠ 0 := Finset.card_ne_zero.2 ⟨v₀, h⟩
    rcases hf j with h' | h'
    · exact h0 h'
    · have : 0 < f j := Nat.pos_of_ne_zero h0
      omega
  · rw [hj]
    refine notin _ fun h => ?_
    have hpos : f j ≠ 0 := Finset.card_ne_zero.2 ⟨v₀, actIn_mono (Nat.le_succ _) h⟩
    rcases hf j with h' | h'
    · exact hpos h'
    have h1 : f j = 1 := by have := Nat.pos_of_ne_zero hpos; omega
    have hne : (actIn (G := G) (c := c) S (2 * j)).Nonempty :=
      Finset.card_pos.1 (by simp only [f] at h1; omega)
    have hc1 := Finset.card_le_card (step_one hc hS (even_two_mul j) hne)
    rw [Finset.card_erase_of_mem (Finset.max'_mem _ _)] at hc1
    have : 0 < (actIn (G := G) (c := c) S (2 * j + 1)).card := Finset.card_pos.2 ⟨v₀, h⟩
    simp only [f] at h1
    omega

end

variable [Fintype V]

open Classical in
/-- The set of nodes of the component of `v` in the subgraph of `G` induced by `R`. -/
noncomputable def comp (G : SimpleGraph V) (R : Set V) (v : V) : Finset V :=
  Finset.univ.filter fun u => (restrict G R).Reachable v u

lemma mem_comp {R : Set V} {v u : V} : u ∈ comp G R v ↔ (restrict G R).Reachable v u := by
  classical
  simp [comp]

lemma closed_comp {v₀ : V} (h0 : σ 0 v₀ = .active) :
    Closed G c (comp G {x | σ 0 x = .active} v₀) := by
  intro w hw u hadj _ hu
  rw [mem_comp] at hw ⊢
  exact hw.trans (Adj.reachable ⟨hadj, restrict_reachable_mem hw h0, hu⟩)

/-- **Lemma 1** (full version; Section 4 of the BA: "the Distributed Greedy MIS Algorithm has round
complexity at most `n` when performed on a graph with `n` nodes"): an initially active node `v₀` has
terminated after `s` rounds, where `s` is the number of nodes of the component of `v₀` in the
subgraph induced by the initially active nodes. -/
theorem greedy_decided (hc : ∀ v, (c v).id = v) {v₀ : V} (h0 : σ 0 v₀ = .active) :
    σ (comp G {x | σ 0 x = .active} v₀).card v₀ ≠ .active :=
  greedy_decided_of_closed hc (closed_comp h0) (mem_comp.2 (Reachable.refl _))

end Podc.GraphAlgorithmsPredictions
