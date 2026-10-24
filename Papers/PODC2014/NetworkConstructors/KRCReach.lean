import Papers.PODC2014.NetworkConstructors.KRCInv

/-!
# Protocol 8 (kRC): reaching the output-stable set, and Theorem 12

From every configuration satisfying `Inv`, the scheduler can reach the closed set `S`
(`reach_S`). The proof decreases the lexicographic measure `μ` =
(number of `l_{k+1}`, number of disconnected ordered pairs, total deficiency `∑ (k − deg)`,
number of leaders):

0. an `l_{k+1}` drops one of its edges (`step_top`);
1. two leaders in one component: walk one to the other, which eliminates it (`step_leaders`);
2. two deficient agents that are not adjacent: they activate their edge (`step_activate`);
3. otherwise, if the network is disconnected, some component `X` is `k`-regular: move its leader
   to an edge `x₁x₂` of `X` lying on a cycle, prepare the other component `Y` (an isolated `q₀`,
   or its leader moved to a deficient agent, or — if `Y` is `k`-regular as well — its leader moved
   to an edge of `Y` on a cycle), open an edge between `X` and `Y` (`(l_k, q₀|l_i|l_k, 0)`), and
   drop the cycle edge(s); this merges `X` and `Y` (`step_merge`).

If none applies, the configuration is in `S`.
-/

namespace Podc.NetworkConstructors.KRC

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem St

section General

variable {V Q : Type*} [Fintype V] [DecidableEq V]

-- Candidate for `Podc/Computability/Distributed/NetworkConstructors/Graph.lean`
theorem two_adj_of_two_le_deg {C : Config V Q} {x : V} (h : 2 ≤ C.deg x) :
    ∃ y z, y ≠ z ∧ C.active.Adj x y ∧ C.active.Adj x z := by
  unfold Config.deg at h
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.1 (by omega :
    1 < (Finset.univ.filter fun v => v ≠ x ∧ C.edge x v = true).card)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy hz
  exact ⟨y, z, hyz, ⟨hy.1.symm, hy.2⟩, ⟨hz.1.symm, hz.2⟩⟩

omit [Fintype V] [DecidableEq V] in
theorem active_eq_of_edge_eq {C D : Config V Q} (h : D.edge = C.edge) : D.active = C.active := by
  ext a b
  simp [Config.active_adj, h]

open Classical in
/-- The number of ordered pairs of vertices that are not connected. -/
noncomputable def unreach (G : SimpleGraph V) : ℕ :=
  (Finset.univ.filter fun p : V × V => ¬ G.Reachable p.1 p.2).card

theorem unreach_le {G G' : SimpleGraph V} (h : ∀ a b, G.Reachable a b → G'.Reachable a b) :
    unreach G' ≤ unreach G := by
  unfold unreach
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact fun hG => hp (h _ _ hG)

theorem unreach_lt {G G' : SimpleGraph V} (h : ∀ a b, G.Reachable a b → G'.Reachable a b)
    {a b : V} (h' : G'.Reachable a b) (hn : ¬ G.Reachable a b) : unreach G' < unreach G := by
  unfold unreach
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨(a, b), by simpa using hn, by simpa using h'⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact fun hG => hp (h _ _ hG)

end General

variable {k : ℕ} (hk : 2 ≤ k) {V : Type*} [Fintype V] [DecidableEq V]

/-- No agent is in `l_{k+1}`. -/
def NoTop (C : Config V (St k)) : Prop := ∀ x, (C.st x).idx ≤ k

/-- The number of agents in state `l_{k+1}`. -/
def nTop (C : Config V (St k)) : ℕ := (Finset.univ.filter fun x => (C.st x).idx = k + 1).card

/-- The total deficiency `∑ (k − index)`. -/
def defic (C : Config V (St k)) : ℕ := ∑ x, (k - (C.st x).idx)

/-- The number of leaders. -/
def nL (C : Config V (St k)) : ℕ := (Finset.univ.filter fun x => (C.st x).isL = true).card

/-- The lexicographic progress measure. -/
noncomputable def μ (C : Config V (St k)) : ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex (nTop C, toLex (unreach C.active, toLex (defic C, nL C)))

theorem μ_lt_iff {C D : Config V (St k)} :
    μ D < μ C ↔ nTop D < nTop C ∨ nTop D = nTop C ∧ (unreach D.active < unreach C.active ∨
      unreach D.active = unreach C.active ∧ (defic D < defic C ∨
        defic D = defic C ∧ nL D < nL C)) := by
  simp [μ, Prod.Lex.toLex_lt_toLex]

omit [DecidableEq V] in
theorem nTop_eq_zero {C : Config V (St k)} (h : NoTop C) : nTop C = 0 := by
  unfold nTop
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _
  have := h x
  omega

/-- Moving a leader along a walk of the active graph (swaps and eliminations): the edges and all
indices are unchanged, the leader arrives at the end of the walk, no new leader appears elsewhere,
and agents outside the component of the start are untouched. -/
theorem walk_leader {G : SimpleGraph V} {u w : V} (p : G.Walk u w) :
    ∀ C : Config V (St k), Inv C → C.active = G → NoTop C → (C.st u).isL = true →
      ∃ D, (kRC k hk).Reachable C D ∧ D.edge = C.edge ∧
        (∀ x, (D.st x).idx = (C.st x).idx) ∧ (D.st w).isL = true ∧
        (∀ x, (D.st x).isL = true → x = w ∨ ((C.st x).isL = true ∧ x ≠ u)) ∧
        (∀ x, ¬ G.Reachable u x → D.st x = C.st x) := by
  induction p with
  | @nil u =>
    intro C _ _ _ hu
    refine ⟨C, .refl, rfl, fun _ => rfl, hu, fun x hx => ?_, fun _ _ => rfl⟩
    by_cases hxu : x = u
    · exact .inl hxu
    · exact .inr ⟨hx, hxu⟩
  | @cons u v w huv p ih =>
    intro C hI hG hN hu
    have hadj : C.active.Adj u v := hG ▸ huv
    have hc : C.edge u v = true := hadj.2
    have hne : u ≠ v := hadj.1
    have hv1 : 1 ≤ (C.st v).idx := by rw [← hI.1]; exact deg_pos_of_adj hadj.symm
    obtain ⟨hL1, hL2⟩ : (δ k hk (C.st u) (C.st v) (C.edge u v)).1.isL = false ∧
        (δ k hk (C.st u) (C.st v) (C.edge u v)).2.1.isL = true := by
      rw [hc]; exact δ_move hk hu (hN u) hv1 (hN v)
    set C1 := (kRC k hk).interact C u v with hC1
    have hsu : C1.st u = (δ k hk (C.st u) (C.st v) (C.edge u v)).1 :=
      Protocol.interact_st_left C u v
    have hsv : C1.st v = (δ k hk (C.st u) (C.st v) (C.edge u v)).2.1 :=
      Protocol.interact_st_right C hne
    have hso : ∀ x, x ≠ u → x ≠ v → C1.st x = C.st x := fun x h1 h2 =>
      Protocol.interact_st_other C h1 h2
    obtain ⟨he, hiu, hiv⟩ : (δ k hk (C.st u) (C.st v) (C.edge u v)).2.2 = C.edge u v ∧
        (δ k hk (C.st u) (C.st v) (C.edge u v)).1.idx = (C.st u).idx ∧
        (δ k hk (C.st u) (C.st v) (C.edge u v)).2.1.idx = (C.st v).idx := by
      rcases δ_kind hk (C.st u) (C.st v) (C.edge u v) with
        ⟨he, hiu, hiv, -⟩ | ⟨hc', -⟩ | ⟨-, -, -, -, htop, -⟩
      · exact ⟨he, hiu, hiv⟩
      · rw [hc] at hc'; exact absurd hc' (by decide)
      · have := hN u; omega
    have hedge : C1.edge = C.edge := Protocol.interact_edge_of_edge_eq he
    have hact : C1.active = G := (Protocol.interact_active_of_edge_eq he).trans hG
    have hidx : ∀ x, (C1.st x).idx = (C.st x).idx := by
      intro x
      by_cases hxu : x = u
      · rw [hxu, hsu, hiu]
      by_cases hxv : x = v
      · rw [hxv, hsv, hiv]
      rw [hso x hxu hxv]
    obtain ⟨D, hR, hDe, hDi, hDw, hDL, hDo⟩ := ih C1 (inv_interact hk hI hne) hact
      (fun x => hidx x ▸ hN x) (by rw [hsv]; exact hL2)
    refine ⟨D, (Protocol.reachable_of_ne (P := kRC k hk) hne).trans hR, hDe.trans hedge,
      fun x => (hDi x).trans (hidx x), hDw, fun x hx => ?_, fun x hx => ?_⟩
    · rcases hDL x hx with h | ⟨h, hxv⟩
      · exact .inl h
      · right
        have hxu : x ≠ u := by
          rintro rfl
          rw [hsu, hL1] at h
          exact absurd h (by decide)
        rw [hso x hxu hxv] at h
        exact ⟨h, hxu⟩
    · have hxu : x ≠ u := fun h => hx (h ▸ .rfl)
      have hxv : x ≠ v := fun h => hx (h ▸ huv.reachable)
      rw [hDo x (fun h => hx (huv.reachable.trans h)), hso x hxu hxv]

/-- Step 0: an agent in `l_{k+1}` drops one of its edges. -/
theorem step_top {C : Config V (St k)} (hI : Inv C) {u : V} (hu : (C.st u).idx = k + 1) :
    ∃ D, (kRC k hk).Reachable C D ∧ Inv D ∧ μ D < μ C := by
  obtain ⟨v, hadj⟩ := exists_adj_of_deg_pos (C := C) (u := u) (by rw [hI.1]; omega)
  have hne : u ≠ v := hadj.1
  have hc : C.edge u v = true := hadj.2
  have hv1 : 1 ≤ (C.st v).idx := by rw [← hI.1]; exact deg_pos_of_adj hadj.symm
  have hdrop := δ_drop hk hu hv1
  rw [← hc] at hdrop
  obtain ⟨hiu, hiv⟩ : (δ k hk (C.st u) (C.st v) (C.edge u v)).1.idx + 1 = (C.st u).idx ∧
      (δ k hk (C.st u) (C.st v) (C.edge u v)).2.1.idx + 1 = (C.st v).idx := by
    rcases δ_kind hk (C.st u) (C.st v) (C.edge u v) with
      ⟨he, -⟩ | ⟨hc', -⟩ | ⟨-, -, hiu, hiv, -⟩
    · rw [hdrop, hc] at he; exact absurd he (by decide)
    · rw [hc] at hc'; exact absurd hc' (by decide)
    · exact ⟨hiu, hiv⟩
  set D := (kRC k hk).interact C u v with hD
  have hsu : D.st u = (δ k hk (C.st u) (C.st v) (C.edge u v)).1 :=
    Protocol.interact_st_left C u v
  have hsv : D.st v = (δ k hk (C.st u) (C.st v) (C.edge u v)).2.1 :=
    Protocol.interact_st_right C hne
  have hso : ∀ x, x ≠ u → x ≠ v → D.st x = C.st x := fun x h1 h2 =>
    Protocol.interact_st_other C h1 h2
  refine ⟨D, Protocol.reachable_of_ne hne, inv_interact hk hI hne, μ_lt_iff.2 (.inl ?_)⟩
  unfold nTop
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨u, by simp [hu], ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsu]
    omega
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    by_cases hxu : x = u
    · rw [hxu, hsu] at hx; omega
    by_cases hxv : x = v
    · rw [hxv, hsv] at hx; have := (C.st v).idx_le; omega
    rwa [hso x hxu hxv] at hx

/-- Step 1: two leaders in one component; one walks to the other and is eliminated. -/
theorem step_leaders {C : Config V (St k)} (hI : Inv C) (hN : NoTop C) {u w : V} (huw : u ≠ w)
    (hu : (C.st u).isL = true) (hw : (C.st w).isL = true) (hr : C.active.Reachable u w) :
    ∃ D, (kRC k hk).Reachable C D ∧ Inv D ∧ μ D < μ C := by
  obtain ⟨p⟩ := hr
  obtain ⟨D, hR, hDe, hDi, -, hDL, -⟩ := walk_leader hk p C hI rfl hN hu
  refine ⟨D, hR, inv_reach hk hI hR, μ_lt_iff.2 (.inr ⟨?_, .inr ⟨?_, .inr ⟨?_, ?_⟩⟩⟩)⟩
  · simp only [nTop, hDi]
  · rw [active_eq_of_edge_eq hDe]
  · simp only [defic, hDi]
  · unfold nL
    have hsub : (Finset.univ.filter fun x => (D.st x).isL = true) ⊆
        (Finset.univ.filter fun x => (C.st x).isL = true).erase u := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hx ⊢
      rcases hDL x hx with rfl | ⟨h, hxu⟩
      · exact ⟨Ne.symm huw, hw⟩
      · exact ⟨hxu, h⟩
    exact (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem (by simpa using hu))

/-- Step 2, one orientation. -/
theorem step_activate_aux {C : Config V (St k)} (hI : Inv C) (hN : NoTop C) {u v : V}
    (huv : u ≠ v) (hu : C.deg u < k) (hv : C.deg v < k) (he : C.edge u v = false)
    (heff : (δ k hk (C.st u) (C.st v) false).2.2 = true) :
    ∃ D, (kRC k hk).Reachable C D ∧ Inv D ∧ μ D < μ C := by
  rw [← he] at heff
  obtain ⟨hiu, hiv⟩ : (δ k hk (C.st u) (C.st v) (C.edge u v)).1.idx = (C.st u).idx + 1 ∧
      (δ k hk (C.st u) (C.st v) (C.edge u v)).2.1.idx = (C.st v).idx + 1 := by
    rcases δ_kind hk (C.st u) (C.st v) (C.edge u v) with
      ⟨he', -⟩ | ⟨-, -, hiu, hiv, -⟩ | ⟨hc', -⟩
    · rw [heff, he] at he'; exact absurd he' (by decide)
    · exact ⟨hiu, hiv⟩
    · rw [he] at hc'; exact absurd hc' (by decide)
  rw [hI.1] at hu hv
  set D := (kRC k hk).interact C u v with hD
  have hsu : D.st u = (δ k hk (C.st u) (C.st v) (C.edge u v)).1 :=
    Protocol.interact_st_left C u v
  have hsv : D.st v = (δ k hk (C.st u) (C.st v) (C.edge u v)).2.1 :=
    Protocol.interact_st_right C huv
  have hso : ∀ x, x ≠ u → x ≠ v → D.st x = C.st x := fun x h1 h2 =>
    Protocol.interact_st_other C h1 h2
  have hact : D.active = C.active ⊔ SimpleGraph.edge u v :=
    Protocol.interact_active_of_edge_true huv heff
  have hidx : ∀ x, (D.st x).idx ≤ k ∧ k - (D.st x).idx ≤ k - (C.st x).idx ∧
      (x = u → k - (D.st x).idx < k - (C.st x).idx) := by
    intro x
    by_cases hxu : x = u
    · subst hxu; rw [hsu, hiu]; omega
    by_cases hxv : x = v
    · subst hxv; rw [hsv, hiv]; exact ⟨by omega, by omega, fun h => absurd h hxu⟩
    rw [hso x hxu hxv]
    exact ⟨hN x, le_rfl, fun h => absurd h hxu⟩
  refine ⟨D, Protocol.reachable_of_ne huv, inv_interact hk hI huv, μ_lt_iff.2 (.inr ⟨?_, ?_⟩)⟩
  · rw [nTop_eq_zero (fun x => (hidx x).1), nTop_eq_zero hN]
  · have h1 : unreach D.active ≤ unreach C.active :=
      unreach_le fun a b h => by rw [hact]; exact h.mono le_sup_left
    have h2 : defic D < defic C :=
      Finset.sum_lt_sum (fun x _ => (hidx x).2.1) ⟨u, Finset.mem_univ _, (hidx u).2.2 rfl⟩
    omega

/-- Step 2: two non-adjacent deficient agents activate their edge. -/
theorem step_activate {C : Config V (St k)} (hI : Inv C) (hN : NoTop C) {u v : V}
    (huv : u ≠ v) (hu : C.deg u < k) (hv : C.deg v < k) (he : C.edge u v = false) :
    ∃ D, (kRC k hk).Reachable C D ∧ Inv D ∧ μ D < μ C := by
  have hu' := hu; have hv' := hv
  rw [hI.1] at hu' hv'
  rcases δ_act hk hu' hv' with h | h
  · exact step_activate_aux hk hI hN huv hu hv he h
  · exact step_activate_aux hk hI hN (Ne.symm huv) hv hu (by rw [C.symm]; exact he) h

end Podc.NetworkConstructors.KRC
