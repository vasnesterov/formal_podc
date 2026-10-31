import Papers.PODC2025.HidingColoringCertification.Theta

/-!
# `r`-forgetful graphs; properties of `θ(5,5,5)`

* `IsForgetful G r`: the definition of the brief announcement / arXiv v1 (Section 1.3): for every
  node `v` and neighbour `u` there is a path `v = v₀, …, v_r` of length `r` such that for every
  `w ∈ N^r(u)` the distance `dist(vᵢ, w)` is (here: strictly) increasing in `i`.
* `IsForgetfulV3 G r`: Definition 22 of arXiv v3 (the authors' corrected definition).
* `not_isForgetful_of_two_le`: under the literal BA definition no graph with an edge is
  `r`-forgetful for `r ≥ 2` (take `w = v₁`, which is in `N²(u)`): the BA's Theorem 4.2 is vacuous
  for `r ≥ 2` as written. (Even the weak, non-strict reading fails: `dist(v₀,v₁) = 1 > 0`.)
* `thetaG_isForgetful`, `thetaG_isForgetfulV3`: `θ(5,5,5)` is 1-forgetful in both senses.
* `thetaG_connected`, `thetaG_two_le_degree`, `thetaG_not_twoRegular`, `thetaG_colorable`.
-/

namespace Podc.HidingColoringCertification

open SimpleGraph

variable {V : Type*}

/-- `r`-forgetfulness as defined in the brief announcement (strict reading). -/
def IsForgetful (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ v u, G.Adj v u → ∃ x, ∃ p : G.Walk v x, p.IsPath ∧ p.length = r ∧
    ∀ w, G.dist u w ≤ r → StrictMono (fun i : Fin (r + 1) => G.dist (p.getVert i) w)

/-- `r`-forgetfulness, Definition 22 of arXiv:2502.13854v3. -/
def IsForgetfulV3 (G : SimpleGraph V) (r : ℕ) : Prop :=
  ∀ v u, G.Adj v u → ∃ x, ∃ p : G.Walk v x, p.IsPath ∧ r ≤ p.length ∧
    ∀ w, G.dist u w ≤ r → G.dist u w < G.dist v w →
      ∀ i ≤ r - G.dist u w, G.dist (p.getVert i) w = G.dist u w + i + 1

/-- A graph is "cycle-like" if it is connected and 2-regular. Every cycle is cycle-like, so
"not cycle-like" is stronger than "not an (even) cycle". -/
def IsCycleLike (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] : Prop :=
  G.Connected ∧ ∀ v, G.degree v = 2

/-- The literal BA definition is unsatisfiable for `r ≥ 2` in any graph with an edge. -/
theorem not_isForgetful_of_two_le {G : SimpleGraph V} {r : ℕ} (hr : 2 ≤ r) {a b : V}
    (hab : G.Adj a b) : ¬ IsForgetful G r := by
  intro h
  obtain ⟨x, p, hp, hlen, hw⟩ := h a b hab
  have h1 : (1 : ℕ) ≤ p.length := by omega
  set v1 := p.getVert 1
  have hadj : G.Adj a v1 := by simpa using p.adj_getVert_succ (i := 0) (by omega)
  have hne : a ≠ v1 := hadj.ne
  have hd : G.dist b v1 ≤ r := by
    have := SimpleGraph.dist_le (Walk.cons hab.symm (Walk.cons hadj Walk.nil))
    simp only [Walk.length_cons, Walk.length_nil] at this
    omega
  have hm := hw v1 hd (show (⟨0, by omega⟩ : Fin (r + 1)) < ⟨1, by omega⟩ from by simp [Fin.lt_def])
  have : G.dist a v1 = 1 := dist_eq_one_iff_adj.2 hadj
  simp only [v1] at this hm
  simp only [Walk.getVert_zero, SimpleGraph.dist_self] at hm
  omega


/-! ### Distance helpers -/

lemma dist_le_two {G : SimpleGraph V} {a x b : V} (h1 : G.Adj a x) (h2 : G.Adj x b) :
    G.dist a b ≤ 2 := by
  simpa using SimpleGraph.dist_le (Walk.cons h1 (Walk.cons h2 Walk.nil))

lemma two_le_dist {G : SimpleGraph V} {a b : V} (hr : G.Reachable a b) (hne : a ≠ b)
    (hna : ¬ G.Adj a b) : 2 ≤ G.dist a b := by
  have h0 : G.dist a b ≠ 0 := fun h => hne ((hr.dist_eq_zero_iff).1 h)
  have h1 : G.dist a b ≠ 1 := fun h => hna (dist_eq_one_iff_adj.1 h)
  omega

lemma three_le_dist {G : SimpleGraph V} {a b : V} (hr : G.Reachable a b) (hne : a ≠ b)
    (hna : ¬ G.Adj a b) (hnc : ∀ x, G.Adj a x → ¬ G.Adj x b) : 3 ≤ G.dist a b := by
  have := two_le_dist hr hne hna
  by_contra hlt
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  have h2 : p.length = 2 := by omega
  have ha := p.adj_getVert_succ (i := 0) (by omega)
  have hb := p.adj_getVert_succ (i := 1) (by omega)
  simp only [Walk.getVert_zero, zero_add] at ha
  rw [show 1 + 1 = p.length by omega, Walk.getVert_length] at hb
  exact hnc _ ha hb

lemma connected_of_potential [Nonempty V] {G : SimpleGraph V} (r : V) (d : V → ℕ)
    (h : ∀ v, v ≠ r → ∃ w, G.Adj v w ∧ d w < d v) : G.Connected := by
  have hreach : ∀ v, G.Reachable r v := by
    intro v
    induction hv : d v using Nat.strong_induction_on generalizing v with
    | _ n ih =>
      by_cases hvr : v = r
      · subst hvr; rfl
      · obtain ⟨w, hw, hlt⟩ := h v hvr
        exact (ih (d w) (hv ▸ hlt) w rfl).trans hw.symm.reachable
  exact (connected_iff _).2 ⟨fun a b => (hreach a).symm.trans (hreach b), inferInstance⟩

/-! ### `θ(5,5,5)` -/

lemma thetaG_connected : thetaG.Connected :=
  connected_of_potential (4 : Fin 14) (fun v => (thetaH v + 1).toNat) (by
    have : ∀ v : Fin 14, v ≠ 4 → ∃ w, thetaG.Adj v w ∧ thetaH w < thetaH v := by decide
    intro v hv
    obtain ⟨w, hw, hlt⟩ := this v hv
    refine ⟨w, hw, ?_⟩
    have : ∀ v : Fin 14, -1 ≤ thetaH v := by decide
    have := this w
    omega)

lemma thetaG_colorable : thetaG.Colorable 2 :=
  ⟨Coloring.mk (fun v => (⟨(thetaH v + 1).toNat % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2))
    (fun {a b} h => by revert a b; decide)⟩

lemma thetaG_two_le_degree (v : Fin 14) : 2 ≤ thetaG.degree v := by
  rw [thetaG_degree]; split_ifs <;> omega

lemma thetaG_minDegree : thetaG.minDegree ≠ 1 := by
  have := le_minDegree_of_forall_le_degree thetaG 2 thetaG_two_le_degree
  omega

lemma thetaG_not_cycleLike : ¬ IsCycleLike thetaG := by
  rintro ⟨-, h⟩
  have := h 4
  rw [thetaG_degree] at this
  simp at this

/-- Combinatorial certificate of 1-forgetfulness (girth ≥ 6 around every edge). -/
lemma thetaG_cert : ∀ v u : Fin 14, thetaG.Adj v u → ∃ v1 ∈ thetaG.neighborFinset v,
    v1 ≠ u ∧ ¬ thetaG.Adj v1 u ∧ ∀ w ∈ thetaG.neighborFinset u, w ≠ v →
      (¬ thetaG.Adj v w ∧ v1 ≠ w ∧ ¬ thetaG.Adj v1 w ∧
        ∀ x ∈ thetaG.neighborFinset v1, ¬ thetaG.Adj x w) := by
  decide

lemma thetaG_reach (a b : Fin 14) : thetaG.Reachable a b := thetaG_connected.preconnected a b

lemma dist_le_one_cases {G : SimpleGraph V} {a b : V} (hr : G.Reachable a b)
    (h : G.dist a b ≤ 1) : a = b ∨ G.Adj a b := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h with h | h
  · exact Or.inl (hr.dist_eq_zero_iff.1 h)
  · exact Or.inr (dist_eq_one_iff_adj.1 h)

/-- `θ(5,5,5)` is 1-forgetful in the sense of the brief announcement (strict reading). -/
theorem thetaG_isForgetful : IsForgetful thetaG 1 := by
  intro v u hvu
  obtain ⟨v1, hv1, hne, hna, hw⟩ := thetaG_cert v u hvu
  rw [mem_neighborFinset] at hv1
  refine ⟨v1, Walk.cons hv1 Walk.nil, ?_, by simp, ?_⟩
  · simp [Walk.cons_isPath_iff, hv1.ne]
  · intro w hdw
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    fin_cases i
    show thetaG.dist v w < thetaG.dist ((Walk.cons hv1 Walk.nil).getVert 1) w
    simp only [Walk.getVert_cons_succ, Walk.getVert_zero]
    rcases dist_le_one_cases (thetaG_reach u w) hdw with rfl | huw
    · rw [dist_eq_one_iff_adj.2 hvu]
      exact two_le_dist (thetaG_reach _ _) hne hna
    · by_cases hwv : w = v
      · subst hwv
        rw [SimpleGraph.dist_self, dist_eq_one_iff_adj.2 hv1.symm]; omega
      · obtain ⟨-, h1, h2, h3⟩ := hw w ((mem_neighborFinset _ _ _).2 huw) hwv
        have := dist_le_two hvu huw
        have := three_le_dist (thetaG_reach v1 w) h1 h2
          (fun x hx => h3 x ((mem_neighborFinset _ _ _).2 hx))
        omega

/-- `θ(5,5,5)` is 1-forgetful in the sense of Definition 22 of arXiv v3. -/
theorem thetaG_isForgetfulV3 : IsForgetfulV3 thetaG 1 := by
  intro v u hvu
  obtain ⟨v1, hv1, hne, hna, hw⟩ := thetaG_cert v u hvu
  rw [mem_neighborFinset] at hv1
  refine ⟨v1, Walk.cons hv1 Walk.nil, ?_, by simp, ?_⟩
  · simp [Walk.cons_isPath_iff, hv1.ne]
  · intro w hdw hlt i hi
    rcases dist_le_one_cases (thetaG_reach u w) hdw with rfl | huw
    · rw [SimpleGraph.dist_self] at hi ⊢
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hi with rfl | rfl
      · simp [dist_eq_one_iff_adj.2 hvu]
      · simp only [Walk.getVert_cons_succ, Walk.getVert_zero]
        have := two_le_dist (thetaG_reach v1 u) hne hna
        have := dist_le_two hv1.symm hvu
        omega
    · rw [dist_eq_one_iff_adj.2 huw] at hlt hi ⊢
      have hi0 : i = 0 := by omega
      subst hi0
      have hwv : w ≠ v := by rintro rfl; simp at hlt
      obtain ⟨h0, -, -, -⟩ := hw w ((mem_neighborFinset _ _ _).2 huw) hwv
      simp only [Walk.getVert_zero]
      have := two_le_dist (thetaG_reach v w) hwv.symm h0
      have := dist_le_two hvu huw
      omega

end Podc.HidingColoringCertification
