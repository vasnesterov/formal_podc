import Papers.PODC2014.NetworkConstructors.CliquesEdges

/-!
# Protocol 9 (`c`-Cliques) constructs `⌊n/c⌋` cliques of order `c` (Theorem 13)

The stable configurations (`Stable`): the invariant holds, no `f_j`, no `l̄_i`, at most one partial
leader, no wrong edge, and every numbered follower has number (= degree) `c − 1`. In such a
configuration every completed component (a leader `l`/`r` with its `c − 1` followers) is a clique
of order `c` with no edges to the outside, the at most `c − 1` remaining agents are in non-output
states, and the only effective interactions move the tokens (`l ↔ r`, `k ↔ l'_k`), which changes
neither the edges nor the output states. `Stable` is reachable from every reachable configuration
(`CliquesReach.lean`, `CliquesEdges.lean`), so `Protocol.constructs_of_reach` applies.

## Main result

* `cliques_constructs`: Theorem 13 — for every `c ≥ 3` and every finite population, Protocol
  `c`-Cliques constructs `⌊n/c⌋` cliques of order `c` (`IsCliquePartition c`).
-/

namespace Podc.NetworkConstructors.Cliques

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem St

variable {c : ℕ} {hc : 3 ≤ c} {V : Type*} [Fintype V] [DecidableEq V]
  {C : Config V (St c)} {p : V → V} {ht : V → ℕ}

/-- The stable configurations, w.r.t. a forest `p`. -/
structure StableWith (C : Config V (St c)) (p : V → V) (ht : V → ℕ) : Prop where
  inv : Inv C p ht
  noFi : NoFi C
  onePartial : OnePartial C
  noLbar : NoLbar C
  noWrong : NoWrong C p
  full : Full C

/-- The stable configurations. -/
def Stable : Set (Config V (St c)) := {C | ∃ p ht, StableWith C p ht}

/-! ### Reachability of the stable set -/

theorem reach_stable {C : Config V (St c)}
    (h : (cliques c hc).Reachable (cliques c hc).initConfig C) :
    ∃ D ∈ Stable, (cliques c hc).Reachable C D := by
  obtain ⟨p, ht, hI⟩ := inv_reachable h
  obtain ⟨D1, h1, hI1, hF1, -, -⟩ := release_all (hc := hc) C ⟨p, ht, hI⟩
  obtain ⟨D2, h2, ⟨⟨p2, ht2, hI2⟩, hF2⟩, hO2⟩ := merge_all (hc := hc) D1 ⟨hI1, hF1⟩
  obtain ⟨D3, h3, ⟨hI3, hF3, hO3⟩, hL3⟩ := count_all (hc := hc) D2 ⟨hI2, hF2, hO2⟩
  obtain ⟨D4, h4, ⟨hI4, hF4, hO4, hL4⟩, hR4⟩ := return_all (hc := hc) D3 ⟨hI3, hF3, hO3, hL3⟩
  obtain ⟨D5, h5, ⟨hI5, hF5, hO5, hL5, hR5⟩, hW5⟩ :=
    cut_all (hc := hc) D4 ⟨hI4, hF4, hO4, hL4, hR4⟩
  obtain ⟨D6, h6, ⟨hI6, hF6, hO6, hL6, -, hW6⟩, hFu6⟩ :=
    complete_all (hc := hc) D5 ⟨hI5, hF5, hO5, hL5, hR5, hW5⟩
  exact ⟨D6, ⟨p2, ht2, ⟨hI6, hF6, hO6, hL6, hW6, hFu6⟩⟩,
    h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))⟩

/-! ### Stable configurations are closed and have constant output -/

/-- Token moves preserve stability. -/
theorem StableWith.of_token (hS : StableWith C p ht) {u v : V} {D : Config V (St c)}
    (hI : Inv D p ht) (he : D.edge = C.edge)
    (hDo : ∀ z, z ≠ u → z ≠ v → D.st z = C.st z)
    (hok : ∀ z, z = u ∨ z = v → (D.st z).isFi = false ∧ (D.st z).isL = false ∧
      (D.st z).isLbar = false ∧ (D.st z).isFol = (C.st z).isFol ∧ (D.st z).idx = (C.st z).idx) :
    StableWith D p ht := by
  have hfol : ∀ z, (D.st z).isFol = (C.st z).isFol := by
    intro z
    by_cases hz : z = u ∨ z = v
    · exact (hok z hz).2.2.2.1
    · push Not at hz; rw [hDo z hz.1 hz.2]
  refine ⟨hI, forall_of_change (P := fun q => q.isFi = false) hS.noFi hDo (hok u (.inl rfl)).1
    (hok v (.inr rfl)).1, onePartial_of_change hS.onePartial hDo (hok u (.inl rfl)).2.1
    (hok v (.inr rfl)).2.1, forall_of_change (P := fun q => q.isLbar = false) hS.noLbar hDo
    (hok u (.inl rfl)).2.2.1 (hok v (.inr rfl)).2.2.1, fun x y hxy hx hy hxy' => ?_,
    fun x hx => ?_⟩
  · rw [hfol] at hx hy; rw [he] at hxy'
    exact hS.noWrong x y hxy hx hy hxy'
  · by_cases hz : x = u ∨ x = v
    · rw [(hok x hz).2.2.2.2]; rw [(hok x hz).2.2.2.1] at hx; exact hS.full x hx
    · push Not at hz; rw [hDo x hz.1 hz.2] at hx ⊢; exact hS.full x hx

/-- One interaction in a stable configuration: stability, edges and output states are kept. -/
theorem StableWith.step (hS : StableWith C p ht) {u v : V} (huv : u ≠ v) :
    StableWith ((cliques c hc).interact C u v) p ht ∧
      ((cliques c hc).interact C u v).edge = C.edge ∧
      ∀ z, (((cliques c hc).interact C u v).st z).out = (C.st z).out := by
  have hI := hS.inv
  obtain ⟨hDu, hDv, hDo⟩ := interact_states (hc := hc) (C := C) huv
  rcases δ_cases hc (C.st u) (C.st v) (C.edge u v) with
    h | ⟨i, hi, j, hj, hu, hv, hji, he⟩ | ⟨i, h1, h2, hu, hv, he⟩ | ⟨i, hi, hu, hv, he⟩ |
    ⟨i, h1, h2, j, h3, h4, hu, hv, hi', hj', he⟩ | ⟨i, h1, h2, hu, hv, he⟩ |
    ⟨i, h1, h2, j, h3, h4, hu, hv, hi', hj', he⟩ | ⟨i, h1, h2, hu, hv, he⟩
  · rw [Protocol.interact_eq_self C h]; exact ⟨hS, rfl, fun _ => rfl⟩
  · exact absurd (hS.onePartial u v (by simp [hu, St.isL]) (by simp [hv, St.isL])) huv
  · have := hS.noFi u; simp [hu, St.isFi] at this
  · have := hS.noLbar u; simp [hu, St.isLbar] at this
  · have := hS.full u (by simp [hu, St.isFol]); simp [hu, St.idx] at this; omega
  · -- the leader visits a follower
    rw [hu, hv, he] at hDu hDv
    simp only [δ] at hDu hDv
    have hedge : ((cliques c hc).interact C u v).edge = C.edge :=
      Protocol.interact_edge_of_edge_eq (by simp only [cliques_δ]; rw [hu, hv, he]; rfl)
    refine ⟨hS.of_token (hI.visit huv hu hv he) hedge hDo ?_, hedge, fun z => ?_⟩
    · rintro z (rfl | rfl)
      · rw [hDu, hu]; simp [St.isFi, St.isL, St.isLbar, St.isFol, St.idx]
      · rw [hDv, hv]; simp [St.isFi, St.isL, St.isLbar, St.isFol, St.idx]
    · by_cases hzu : z = u
      · subst hzu; rw [hDu, hu]; rfl
      by_cases hzv : z = v
      · subst hzv; rw [hDv, hv]; rfl
      rw [hDo z hzu hzv]
  · -- two visited followers over an active edge: impossible (they would be in the same component)
    exfalso
    have hpe := hS.noWrong u v huv (by simp [hu, St.isFol]) (by simp [hv, St.isFol]) he
    have hsub : ({u, v} : Finset V) ⊆ (kids p (p u)).filter fun w => (C.st w).isVis = true := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact Finset.mem_filter.2 ⟨hI.mem_kids_parent (by simp [hu, St.isFol]), by simp [hu, St.isVis]⟩
      · exact Finset.mem_filter.2 ⟨hpe ▸ hI.mem_kids_parent (by simp [hv, St.isFol]),
          by simp [hv, St.isVis]⟩
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_pair huv, hI.nvis] at h2
    cases h' : C.st (p u) <;> simp [h', St.nvis] at h2
  · -- the token returns
    rw [hu, hv, he] at hDu hDv
    simp only [δ] at hDu hDv
    have hedge : ((cliques c hc).interact C u v).edge = C.edge :=
      Protocol.interact_edge_of_edge_eq (by simp only [cliques_δ]; rw [hu, hv, he]; rfl)
    refine ⟨hS.of_token (hI.back huv hu hv he) hedge hDo ?_, hedge, fun z => ?_⟩
    · rintro z (rfl | rfl)
      · rw [hDu, hu]; simp [St.isFi, St.isL, St.isLbar, St.isFol, St.idx]
      · rw [hDv, hv]; simp [St.isFi, St.isL, St.isLbar, St.isFol, St.idx]
    · by_cases hzu : z = u
      · subst hzu; rw [hDu, hu]; rfl
      by_cases hzv : z = v
      · subst hzv; rw [hDv, hv]; rfl
      rw [hDo z hzu hzv]

theorem stable_trap : IsTrap (cliques c hc).Step (Stable : Set (Config V (St c))) := by
  rintro C D ⟨p, ht, hS⟩ ⟨u, v, huv, rfl⟩
  exact ⟨p, ht, (hS.step huv).1⟩

theorem stable_output {C D : Config V (St c)} (hC : C ∈ Stable) (h : (cliques c hc).Step C D) :
    (cliques c hc).output D = (cliques c hc).output C := by
  obtain ⟨p, ht, hS⟩ := hC
  obtain ⟨u, v, huv, rfl⟩ := h
  obtain ⟨-, he, hout⟩ := hS.step (hc := hc) huv
  exact Protocol.output_eq_of _ (fun z => hout z) he

/-! ### The output of a stable configuration is a clique partition -/

namespace StableWith

theorem parent_state (hS : StableWith C p ht) {x : V} (hx : (C.st x).isFol = true) :
    C.st (p x) = .lead ∨ C.st (p x) = .r := by
  have hI := hS.inv
  have := hI.card_filter_pos (hI.mem_kids_parent hx) (P := St.isFol) hx
  rw [hI.nfol] at this
  have hl := hS.noLbar (p x)
  cases h' : C.st (p x) <;> simp_all [St.nfol, St.isLbar]

theorem kids_fol (hS : StableWith C p ht) {a : V} (ha : C.st a = .lead ∨ C.st a = .r) :
    (kids p a).card = c - 1 ∧ ∀ w ∈ kids p a, (C.st w).isFol = true := by
  have hI := hS.inv
  have hk : (kids p a).card = c - 1 := by rw [hI.nkids]; rcases ha with h | h <;> rw [h] <;> rfl
  refine ⟨hk, Finset.filter_card_eq ?_⟩
  rw [hI.nfol, hk]; rcases ha with h | h <;> rw [h] <;> rfl

theorem out_iff (q : St c) : q.out = true ↔ q.isFol = true ∨ q = .lead ∨ q = .r := by
  cases q <;> simp [St.out, St.isFol]

theorem nbr_out (hS : StableWith C p ht) {x y : V} (hx : (C.st x).out = true) (hxy : y ≠ x)
    (he : C.edge x y = true) : (C.st y).out = true := by
  have hI := hS.inv
  rw [out_iff] at hx ⊢
  rcases hx with hx | hx
  · by_cases hy : (C.st y).isFol = true
    · exact .inl hy
    · have := (hI.edge_fol_nonfol (Ne.symm hxy) hx (by simpa using hy)).1 he
      subst this; exact .inr (hS.parent_state hx)
  · have hpx : p x = x := hI.p_eq (by rcases hx with h | h <;> simp [h, St.isRoot])
    have hxf : (C.st x).isFol = false := by rcases hx with h | h <;> simp [h, St.isFol]
    rcases (hI.edge x y (Ne.symm hxy) (by simp [hxf])).1 he with h | h
    · exact absurd (hpx.symm.trans h) (Ne.symm hxy)
    · exact .inl ((hS.kids_fol hx).2 y (mem_kids.2 ⟨h, hxy⟩))

theorem deg_out (hS : StableWith C p ht) {x : V} (hx : (C.st x).out = true) :
    C.deg x = c - 1 := by
  have hI := hS.inv
  rw [out_iff] at hx
  rcases hx with hx | hx
  · rw [hI.deg x hx, hS.full x hx]
  · have hpx : p x = x := hI.p_eq (by rcases hx with h | h <;> simp [h, St.isRoot])
    have hxf : (C.st x).isFol = false := by rcases hx with h | h <;> simp [h, St.isFol]
    rw [← (hS.kids_fol hx).1]
    unfold Config.deg
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_kids]
    constructor
    · rintro ⟨hyx, he⟩
      rcases (hI.edge x y (Ne.symm hyx) (by simp [hxf])).1 he with h | h
      · exact absurd (hpx.symm.trans h) (Ne.symm hyx)
      · exact ⟨h, hyx⟩
    · rintro ⟨h, hyx⟩
      exact ⟨hyx, (hI.edge x y (Ne.symm hyx) (by simp [hxf])).2 (.inr h)⟩

/-- Followers of the same leader are adjacent (the components are cliques). -/
theorem clique (hS : StableWith C p ht) {x y : V} (hx : (C.st x).isFol = true)
    (hxy : x ≠ y) (hp : p x = p y) (hy : (C.st y).isFol = true) : C.edge x y = true := by
  have hI := hS.inv
  have ha := hS.parent_state hx
  generalize hav : p x = a at ha hp
  have haf : (C.st a).isFol = false := by rcases ha with h | h <;> simp [h, St.isFol]
  have hka := hS.kids_fol ha
  have hxa : x ∈ kids p a := hav ▸ hI.mem_kids_parent hx
  have haa : a ∉ kids p a := by simp
  have hsub : (Finset.univ.filter fun z => z ≠ x ∧ C.edge x z = true) ⊆
      insert a ((kids p a).erase x) := by
    intro z hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    by_cases hzf : (C.st z).isFol = true
    · have hpz : p z = a := (hS.noWrong x z (Ne.symm hz.1) hx hzf hz.2).symm.trans hav
      exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hz.1, mem_kids.2 ⟨hpz,
        fun h => by rw [h, haf] at hzf; exact Bool.noConfusion hzf⟩⟩)
    · have := (hI.edge_fol_nonfol (Ne.symm hz.1) hx (by simpa using hzf)).1 hz.2
      rw [hav] at this
      rw [← this]; exact Finset.mem_insert_self _ _
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_insert_of_notMem (fun h => haa (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hxa, hka.1]
    have := hS.deg_out ((out_iff _).2 (.inl hx))
    unfold Config.deg at this
    have hpos : 0 < (kids p a).card := Finset.card_pos.2 ⟨x, hxa⟩
    rw [this]; omega)
  have hy' : y ∈ insert a ((kids p a).erase x) :=
    Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨Ne.symm hxy, mem_kids.2 ⟨hp.symm,
      fun h => by rw [h, haf] at hy; exact Bool.noConfusion hy⟩⟩)
  rw [← heq] at hy'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy'
  exact hy'.2

/-- The component of an output agent: its leader. -/
def comp (C : Config V (St c)) (p : V → V) (x : V) : V := if (C.st x).isFol then p x else x

theorem adj_iff (hS : StableWith C p ht) {x y : V} (hx : (C.st x).out = true)
    (hy : (C.st y).out = true) (hxy : x ≠ y) : C.edge x y = true ↔ comp C p x = comp C p y := by
  have hI := hS.inv
  have hroot : ∀ z, (C.st z).isFol = false → (C.st z).out = true → p z = z := fun z hf ho => by
    rw [out_iff, hf] at ho
    exact hI.p_eq (by rcases ho with h | h | h <;> simp_all [St.isRoot])
  unfold comp
  by_cases hxf : (C.st x).isFol = true <;> by_cases hyf : (C.st y).isFol = true
  · simp only [hxf, hyf, ite_true]
    exact ⟨hS.noWrong x y hxy hxf hyf, fun h => hS.clique hxf hxy h hyf⟩
  · simp only [hxf, hyf, ite_true, Bool.false_eq_true, ite_false]
    exact hI.edge_fol_nonfol hxy hxf (by simpa using hyf)
  · simp only [hxf, hyf, ite_true, Bool.false_eq_true, ite_false]
    rw [C.symm]
    exact (hI.edge_fol_nonfol (Ne.symm hxy) hyf (by simpa using hxf)).trans eq_comm
  · simp only [hxf, hyf, Bool.false_eq_true, ite_false]
    rw [hI.edge x y hxy (by simp_all), hroot x (by simpa using hxf) hx,
      hroot y (by simpa using hyf) hy]
    exact ⟨fun h => h.elim id Eq.symm, fun h => .inl h⟩

/-- The parent of an `f` is the (unique) partial leader. -/
theorem parent_of_f (hS : StableWith C p ht) {w : V} (hw : C.st w = .f) :
    (C.st (p w)).isL = true := by
  have hI := hS.inv
  have hpw : p w ≠ w := hI.p_ne (by simp [hw, St.isRoot])
  have hk : w ∈ kids p (p w) := mem_kids.2 ⟨rfl, hpw.symm⟩
  have hfi := hS.noFi (p w)
  have hlb := hS.noLbar (p w)
  cases h : C.st (p w) with
  | l i hi => rfl
  | lead => have := (hS.kids_fol (.inl h)).2 w hk; simp [hw, St.isFol] at this
  | r => have := (hS.kids_fol (.inr h)).2 w hk; simp [hw, St.isFol] at this
  | fi j h1 h2 => simp [h, St.isFi] at hfi
  | lbar i hi => simp [h, St.isLbar] at hlb
  | f => have := hI.kids_empty (x := p w) (by simp [h, St.nkids]); simp [this] at hk
  | num k h1 h2 => have := hI.kids_empty (x := p w) (by simp [h, St.nkids]); simp [this] at hk
  | lp k h1 h2 => have := hI.kids_empty (x := p w) (by simp [h, St.nkids]); simp [this] at hk

/-- At most `c − 1` agents are not in output states. -/
theorem card_nonout (hS : StableWith C p ht) (hc2 : 2 ≤ c) :
    (Finset.univ.filter fun x => ¬(C.st x).out = true).card ≤ c - 1 := by
  have hI := hS.inv
  have hst : ∀ w, ¬(C.st w).out = true → (C.st w).isL = true ∨ C.st w = .f := by
    intro w hw
    have h1 := hS.noFi w
    have h2 := hS.noLbar w
    cases h : C.st w <;> simp_all [St.out, St.isL, St.isFi, St.isLbar]
  by_cases hz : ∃ z, (C.st z).isL = true
  · obtain ⟨z, hz⟩ := hz
    obtain ⟨i, hi, hzi⟩ := st_eq_l hz
    have hsub : (Finset.univ.filter fun x => ¬(C.st x).out = true) ⊆ insert z (kids p z) := by
      intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      rcases hst w hw with h | h
      · rw [hS.onePartial w z h hz]; exact Finset.mem_insert_self _ _
      · have hpw := hS.onePartial _ z (hS.parent_of_f h) hz
        exact Finset.mem_insert_of_mem (mem_kids.2 ⟨hpw, fun hwz => by
          rw [hwz, hzi] at h; cases h⟩)
    have := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    rw [hI.nkids, hzi] at this
    simp only [St.nkids] at this
    omega
  · push Not at hz
    have : (Finset.univ.filter fun x => ¬(C.st x).out = true) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro w _ hw
      rcases hst w hw with h | h
      · exact absurd h (by simp [hz w])
      · exact absurd (hS.parent_of_f h) (by simp [hz (p w)])
    rw [this]; simp

/-- The number of output agents is `c ⌊n/c⌋`. -/
theorem card_out (hS : StableWith C p ht) (hc2 : 2 ≤ c) :
    (Finset.univ.filter fun x => (C.st x).out = true).card = c * (Fintype.card V / c) := by
  have hI := hS.inv
  have hO : (Finset.univ.filter fun x => (C.st x).out = true).card =
      c * (Finset.univ.filter fun x => C.st x = .lead ∨ C.st x = .r).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := comp C p)
      (t := Finset.univ.filter fun x => C.st x = .lead ∨ C.st x = .r)]
    · rw [Finset.sum_const_nat (m := c), mul_comm]
      intro a ha
      rw [Finset.mem_filter] at ha
      replace ha := ha.2
      have haf : (C.st a).isFol = false := by rcases ha with h | h <;> simp [h, St.isFol]
      have hpa : p a = a := hI.p_eq (by rcases ha with h | h <;> simp [h, St.isRoot])
      have : (Finset.univ.filter fun x => (C.st x).out = true).filter
          (fun x => comp C p x = a) = insert a (kids p a) := by
        ext x
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_insert, mem_kids]
        simp only [Finset.mem_univ, true_and, comp]
        constructor
        · rintro ⟨hx, hc⟩
          split_ifs at hc with hxf
          · exact .inr ⟨hc, fun h => by rw [h, haf] at hxf; exact Bool.noConfusion hxf⟩
          · exact .inl hc
        · rintro (rfl | ⟨hpx, hxa⟩)
          · exact ⟨(out_iff _).2 (.inr ha), by simp [haf]⟩
          · have hxf := (hS.kids_fol ha).2 x (mem_kids.2 ⟨hpx, hxa⟩)
            exact ⟨(out_iff _).2 (.inl hxf), by simp [hxf, hpx]⟩
      rw [this, Finset.card_insert_of_notMem (by simp), (hS.kids_fol ha).1]
      omega
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_filter] at hx
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold comp
      rcases (out_iff _).1 hx.2 with hxf | hxr
      · simp only [hxf, ite_true]; exact hS.parent_state hxf
      · have hxf : (C.st x).isFol = false := by rcases hxr with h | h <;> simp [h, St.isFol]
        simp only [hxf, Bool.false_eq_true, ite_false]; exact hxr
  have hn := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun x => (C.st x).out = true)
  rw [Finset.card_univ] at hn
  have hN := hS.card_nonout hc2
  have hdiv : Fintype.card V / c =
      (Finset.univ.filter fun x => C.st x = .lead ∨ C.st x = .r).card := by
    rw [← hn, hO, Nat.add_comm, Nat.add_mul_div_left _ _ (by omega),
      Nat.div_eq_of_lt (by omega), zero_add]
  rw [hO, hdiv]

/-- **The output of a stable configuration is a partition into cliques of order `c`.** -/
theorem isCliquePartition (hS : StableWith C p ht) :
    IsCliquePartition c ((cliques c hc).output C) := by
  have hI := hS.inv
  refine ⟨?_, fun x hx => ?_, fun x y z hxy hyz hxz => ?_⟩
  · have : ((cliques c hc).output C).verts =
        ↑(Finset.univ.filter fun x => (C.st x).out = true) := by
      ext x; simp [Protocol.output]
    rw [this, Set.ncard_coe_finset, hS.card_out (by omega)]
  · have hx' : (C.st x).out = true := hx
    have : ((cliques c hc).output C).neighborSet x =
        ↑(Finset.univ.filter fun y => y ≠ x ∧ C.edge x y = true) := by
      ext y
      rw [Protocol.output_neighborSet]
      simp only [cliques_out, Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2, -, -⟩; exact ⟨Ne.symm h1, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨Ne.symm h1, h2, hx', hS.nbr_out hx' h1 h2⟩
    rw [this, Set.ncard_coe_finset]
    exact hS.deg_out hx'
  · obtain ⟨hxy', hexy, hx, hy⟩ := hxy
    obtain ⟨hyz', heyz, -, hz⟩ := hyz
    refine ⟨hxz, ?_, hx, hz⟩
    rw [hS.adj_iff hx hz hxz]
    exact ((hS.adj_iff hx hy hxy').1 hexy).trans ((hS.adj_iff hy hz hyz').1 heyz)

end StableWith

/-- **Theorem 13 of Michail–Spirakis (PODC 2014).** For every `c ≥ 3`, Protocol `c`-Cliques
(Protocol 9) constructs `⌊n/c⌋` cliques of order `c`: in every globally fair execution on any
finite population, the output graph (output states `l, r, 1, …, c − 1, l'_1, …, l'_{c−1}`)
stabilizes to a disjoint union of `⌊n/c⌋` cliques of order `c`. -/
theorem cliques_constructs (c : ℕ) (hc : 3 ≤ c) (V : Type*) [Fintype V] [DecidableEq V] :
    (cliques c hc).Constructs (V := V) (IsCliquePartition c) :=
  (cliques c hc).constructs_of_reach Stable stable_trap (fun _ _ hC h => stable_output hC h)
    (fun _ ⟨_, _, hS⟩ => hS.isCliquePartition) (fun _ h => reach_stable h)

end Podc.NetworkConstructors.Cliques
