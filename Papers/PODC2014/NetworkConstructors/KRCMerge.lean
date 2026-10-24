import Papers.PODC2014.NetworkConstructors.KRCReach

/-!
# Protocol 8 (kRC): merging components, and Theorem 12

Step 3 of the reachability argument (`step_merge`): a `k`-regular component `X` is merged with
another component `Y` by opening an edge between them and dropping an edge of `X` (and of `Y`, if
`Y` is `k`-regular too) that lies on a cycle. Then `reach_S` and **Theorem 12**
(`kRC_constructs`).
-/

namespace Podc.NetworkConstructors.KRC

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem St

variable {k : ℕ} (hk : 2 ≤ k) {V : Type*} [Fintype V] [DecidableEq V]

/-- Preparing the component `Y` of `b` (disjoint from the component of `a`) for a merge: either
an agent `y` of `Y` is deficient and holds `q₀` or a leader, or `Y` is `k`-regular and its leader
sits at an endpoint `y` of an edge `yy₂` of `Y` lying on a cycle. -/
theorem prepare_far {C : Config V (St k)} (hI : Inv C) (hN : NoTop C) {a b : V}
    (hab : ¬ C.active.Reachable a b) :
    ∃ C0 y, (kRC k hk).Reachable C C0 ∧ C0.edge = C.edge ∧ NoTop C0 ∧
      (∀ x, C.active.Reachable a x → C0.st x = C.st x) ∧ C.active.Reachable b y ∧
      ((((C0.st y).idx = 0 ∨ (C0.st y).isL = true) ∧ (C0.st y).idx < k) ∨
       ((C0.st y).isL = true ∧ (C0.st y).idx = k ∧
         ∃ y2, C.active.Adj y y2 ∧ (C.active \ SimpleGraph.edge y y2).Reachable y y2)) := by
  by_cases hdef : ∃ y, C.active.Reachable b y ∧ C.deg y < k
  · obtain ⟨y, hby, hy⟩ := hdef
    by_cases hy0 : C.deg y = 0
    · exact ⟨C, y, .refl, rfl, hN, fun _ _ => rfl, hby,
        .inl ⟨.inl (by rw [← hI.1]; exact hy0), by rw [← hI.1]; exact hy⟩⟩
    · obtain ⟨ℓ, hℓ, hyℓ⟩ := hI.2 y (Nat.pos_of_ne_zero hy0)
      obtain ⟨p⟩ := hyℓ.symm
      obtain ⟨C0, hR, hE, hi, hL, -, ho⟩ := walk_leader hk p C hI rfl hN hℓ
      refine ⟨C0, y, hR, hE, fun x => (hi x) ▸ hN x, fun x hax => ho x fun hℓx =>
        hab (hax.trans (hℓx.symm.trans (hyℓ.symm.trans hby.symm))), hby,
        .inl ⟨.inr hL, by rw [hi, ← hI.1]; exact hy⟩⟩
  · push Not at hdef
    have hreg : ∀ y, C.active.Reachable b y → C.deg y = k := fun y hy =>
      le_antisymm (hI.1 y ▸ hN y) (hdef y hy)
    obtain ⟨y1, y2, hby1, hy12, hcyc⟩ := exists_adj_reachable_sdiff_edge (G := C.active) (a := b)
      (fun x hx => two_adj_of_two_le_deg (by rw [hreg x hx]; exact hk))
    obtain ⟨ℓ, hℓ, hyℓ⟩ := hI.2 y1 (by rw [hreg y1 hby1]; omega)
    obtain ⟨p⟩ := hyℓ.symm
    obtain ⟨C0, hR, hE, hi, hL, -, ho⟩ := walk_leader hk p C hI rfl hN hℓ
    refine ⟨C0, y1, hR, hE, fun x => (hi x) ▸ hN x, fun x hax => ho x fun hℓx =>
      hab (hax.trans (hℓx.symm.trans (hyℓ.symm.trans hby1.symm))), hby1,
      .inr ⟨hL, by rw [hi, ← hI.1, hreg y1 hby1], y2, hy12, hcyc⟩⟩

/-- Step 3: merging a `k`-regular component (that of `a`) with another component. -/
theorem step_merge {C : Config V (St k)} (hI : Inv C) (hN : NoTop C) {a b : V}
    (hab : ¬ C.active.Reachable a b) (hX : ∀ x, C.active.Reachable a x → C.deg x = k) :
    ∃ D, (kRC k hk).Reachable C D ∧ Inv D ∧ μ D < μ C := by
  set G := C.active with hG
  have hsep : ∀ x z, G.Reachable a x → G.Reachable b z → ¬ G.Reachable x z :=
    fun x z hx hz h => hab (hx.trans (h.trans hz.symm))
  have hsepne : ∀ x z, G.Reachable a x → G.Reachable b z → x ≠ z :=
    fun x z hx hz h => hsep x z hx hz (h ▸ .rfl)
  -- an edge `x₁x₂` of `X` on a cycle
  obtain ⟨x1, x2, hax1, hx12, hcyc⟩ := exists_adj_reachable_sdiff_edge (G := G) (a := a)
    (fun x hx => two_adj_of_two_le_deg (by rw [hX x hx]; exact hk))
  have hax2 : G.Reachable a x2 := hax1.trans hx12.reachable
  -- prepare `Y`
  obtain ⟨C0, y, hR0, hE0, hN0, hX0, hby, hYy⟩ := prepare_far hk hI hN hab
  have hI0 : Inv C0 := inv_reach hk hI hR0
  have hG0 : C0.active = G := active_eq_of_edge_eq hE0
  -- move the leader of `X` to `x₁`
  obtain ⟨ℓ, hℓ, hx1ℓ⟩ := hI.2 x1 (by rw [hX x1 hax1]; omega)
  have haℓ : G.Reachable a ℓ := hax1.trans hx1ℓ
  obtain ⟨p⟩ := hx1ℓ.symm
  obtain ⟨C1, hR1, hE1, hi1, hL1, -, ho1⟩ :=
    walk_leader hk p C0 hI0 hG0 hN0 (by rw [hX0 ℓ haℓ]; exact hℓ)
  have hI1 : Inv C1 := inv_reach hk hI0 hR1
  have hE1' : C1.edge = C.edge := hE1.trans hE0
  have hfar : ∀ z, G.Reachable b z → C1.st z = C0.st z := fun z hz =>
    ho1 z (fun h => hsep ℓ z haℓ hz h)
  have hN1 : NoTop C1 := fun x => (hi1 x) ▸ hN0 x
  have hx1k : (C1.st x1).idx = k := by rw [hi1, hX0 x1 hax1, ← hI.1, hX x1 hax1]
  have hx2k : (C1.st x2).idx = k := by rw [hi1, hX0 x2 hax2, ← hI.1, hX x2 hax2]
  have hx1y : x1 ≠ y := hsepne x1 y hax1 hby
  have hx2y : x2 ≠ y := hsepne x2 y hax2 hby
  have hx12' : x1 ≠ x2 := hx12.ne
  -- open the edge `x₁y`
  have he1 : C1.edge x1 y = false := by
    rw [hE1']
    by_contra h
    exact hsep x1 y hax1 hby (show G.Adj x1 y from ⟨hx1y, by simpa using h⟩).reachable
  have hopen : (δ k hk (C1.st x1) (C1.st y) (C1.edge x1 y)).2.2 = true := by
    rw [he1]
    refine δ_open hk hL1 hx1k ?_
    rw [hfar y hby]
    rcases hYy with ⟨h0 | hL, hlt⟩ | ⟨hL, heq, -⟩
    · exact .inl h0
    · exact .inr ⟨hL, hlt.le⟩
    · exact .inr ⟨hL, heq.le⟩
  obtain ⟨hiu2, hiv2⟩ : (δ k hk (C1.st x1) (C1.st y) (C1.edge x1 y)).1.idx = (C1.st x1).idx + 1 ∧
      (δ k hk (C1.st x1) (C1.st y) (C1.edge x1 y)).2.1.idx = (C1.st y).idx + 1 := by
    rcases δ_kind hk (C1.st x1) (C1.st y) (C1.edge x1 y) with
      ⟨he', -⟩ | ⟨-, -, hiu, hiv, -⟩ | ⟨hc', -⟩
    · rw [hopen, he1] at he'; exact absurd he' (by decide)
    · exact ⟨hiu, hiv⟩
    · rw [he1] at hc'; exact absurd hc' (by decide)
  set C2 := (kRC k hk).interact C1 x1 y with hC2
  have hs2u : C2.st x1 = (δ k hk (C1.st x1) (C1.st y) (C1.edge x1 y)).1 :=
    Protocol.interact_st_left C1 x1 y
  have hs2v : C2.st y = (δ k hk (C1.st x1) (C1.st y) (C1.edge x1 y)).2.1 :=
    Protocol.interact_st_right C1 hx1y
  have hs2o : ∀ x, x ≠ x1 → x ≠ y → C2.st x = C1.st x := fun x h1 h2 =>
    Protocol.interact_st_other C1 h1 h2
  have hact2 : C2.active = G ⊔ SimpleGraph.edge x1 y := by
    rw [Protocol.interact_active_of_edge_true hx1y hopen, active_eq_of_edge_eq hE1']
  have hI2 : Inv C2 := inv_interact hk hI1 hx1y
  -- drop the cycle edge `x₁x₂`
  have he2 : C2.edge x1 x2 = true := by
    rw [hC2, Protocol.interact_edge_other C1 (by
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact hx2y h
      · exact hx1y h), hE1']
    exact hx12.2
  have hdrop : (δ k hk (C2.st x1) (C2.st x2) (C2.edge x1 x2)).2.2 = false := by
    rw [he2]
    refine δ_drop hk ?_ ?_
    · rw [hs2u, hiu2, hx1k]
    · rw [hs2o x2 hx12'.symm hx2y, hx2k]; omega
  obtain ⟨hiu3, hiv3⟩ : (δ k hk (C2.st x1) (C2.st x2) (C2.edge x1 x2)).1.idx + 1 =
        (C2.st x1).idx ∧
      (δ k hk (C2.st x1) (C2.st x2) (C2.edge x1 x2)).2.1.idx + 1 = (C2.st x2).idx := by
    rcases δ_kind hk (C2.st x1) (C2.st x2) (C2.edge x1 x2) with
      ⟨he', -⟩ | ⟨hc', -⟩ | ⟨-, -, hiu, hiv, -⟩
    · rw [hdrop, he2] at he'; exact absurd he' (by decide)
    · rw [he2] at hc'; exact absurd hc' (by decide)
    · exact ⟨hiu, hiv⟩
  set C3 := (kRC k hk).interact C2 x1 x2 with hC3
  have hs3u : C3.st x1 = (δ k hk (C2.st x1) (C2.st x2) (C2.edge x1 x2)).1 :=
    Protocol.interact_st_left C2 x1 x2
  have hs3v : C3.st x2 = (δ k hk (C2.st x1) (C2.st x2) (C2.edge x1 x2)).2.1 :=
    Protocol.interact_st_right C2 hx12'
  have hs3o : ∀ x, x ≠ x1 → x ≠ x2 → C3.st x = C2.st x := fun x h1 h2 =>
    Protocol.interact_st_other C2 h1 h2
  have hact3 : C3.active = (G ⊔ SimpleGraph.edge x1 y) \ SimpleGraph.edge x1 x2 := by
    rw [Protocol.interact_active_of_edge_false hdrop, hact2]
  have hI3 : Inv C3 := inv_interact hk hI2 hx12'
  have hR3 : (kRC k hk).Reachable C C3 :=
    hR0.trans (hR1.trans ((Protocol.reachable_of_ne hx1y).trans (Protocol.reachable_of_ne hx12')))
  have hk1 : (C2.st x1).idx = k + 1 := by rw [hs2u, hiu2, hx1k]
  have hk2 : (C2.st x2).idx = k := by rw [hs2o x2 hx12'.symm hx2y, hx2k]
  have hN3 : ∀ x, x ≠ y → (C3.st x).idx ≤ k := by
    intro x hxy
    by_cases h1 : x = x1
    · rw [h1, hs3u]; omega
    by_cases h2 : x = x2
    · rw [h2, hs3v]; omega
    rw [hs3o x h1 h2, hs2o x h1 hxy]
    exact hN1 x
  have hy3 : (C3.st y).idx = (C0.st y).idx + 1 := by
    rw [hs3o y hx1y.symm hx2y.symm, hs2v, hiv2, hfar y hby]
  have hadj3 : C3.active.Adj x1 y := by
    rw [hact3, SimpleGraph.sdiff_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj,
      SimpleGraph.edge_adj]
    refine ⟨.inr ⟨.inl ⟨rfl, rfl⟩, hx1y⟩, ?_⟩
    rintro ⟨⟨-, h⟩ | ⟨h, -⟩, -⟩
    · exact hx2y h.symm
    · exact hx12' h
  have hmono3 : ∀ p q, G.Reachable p q → (G \ SimpleGraph.edge x1 x2).Reachable p q :=
    fun p q h => reachable_sdiff_edge_of_reachable hcyc h
  have hle3 : G \ SimpleGraph.edge x1 x2 ≤ C3.active := by
    rw [hact3]; exact sdiff_le_sdiff_right le_sup_left
  rcases hYy with ⟨-, hlt⟩ | ⟨-, heq, y2, hy12, hcyc2⟩
  · -- `y` was deficient: done
    refine ⟨C3, hR3, hI3, μ_lt_iff.2 (.inr ⟨?_, .inl ?_⟩)⟩
    · rw [nTop_eq_zero hN, nTop_eq_zero (C := C3) (fun x => ?_)]
      by_cases hxy : x = y
      · rw [hxy, hy3]; omega
      · exact hN3 x hxy
    · exact unreach_lt (fun p q h => (hmono3 p q h).mono hle3) hadj3.reachable
        (hsep x1 y hax1 hby)
  · -- `Y` is `k`-regular: drop the cycle edge `yy₂` too
    have hby2 : G.Reachable b y2 := hby.trans hy12.reachable
    have hy2x1 : y2 ≠ x1 := (hsepne x1 y2 hax1 hby2).symm
    have hy2x2 : y2 ≠ x2 := (hsepne x2 y2 hax2 hby2).symm
    have hyy2 : y ≠ y2 := hy12.ne
    have he3 : C3.edge y y2 = true := by
      rw [hC3, Protocol.interact_edge_other C2 (by
        rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact hx1y h.symm
        · exact hx2y h.symm), hC2, Protocol.interact_edge_other C1 (by
        rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact hx1y h.symm
        · exact hy2x1 h), hE1']
      exact hy12.2
    have hadj : C3.active.Adj y y2 := ⟨hyy2, he3⟩
    have hdrop' : (δ k hk (C3.st y) (C3.st y2) (C3.edge y y2)).2.2 = false := by
      rw [he3]
      refine δ_drop hk (by rw [hy3, heq]) ?_
      rw [← hI3.1]
      exact deg_pos_of_adj hadj.symm
    obtain ⟨hiu4, hiv4⟩ : (δ k hk (C3.st y) (C3.st y2) (C3.edge y y2)).1.idx + 1 =
          (C3.st y).idx ∧
        (δ k hk (C3.st y) (C3.st y2) (C3.edge y y2)).2.1.idx + 1 = (C3.st y2).idx := by
      rcases δ_kind hk (C3.st y) (C3.st y2) (C3.edge y y2) with
        ⟨he', -⟩ | ⟨hc', -⟩ | ⟨-, -, hiu, hiv, -⟩
      · rw [hdrop', he3] at he'; exact absurd he' (by decide)
      · rw [he3] at hc'; exact absurd hc' (by decide)
      · exact ⟨hiu, hiv⟩
    set C4 := (kRC k hk).interact C3 y y2 with hC4
    have hs4u : C4.st y = (δ k hk (C3.st y) (C3.st y2) (C3.edge y y2)).1 :=
      Protocol.interact_st_left C3 y y2
    have hs4v : C4.st y2 = (δ k hk (C3.st y) (C3.st y2) (C3.edge y y2)).2.1 :=
      Protocol.interact_st_right C3 hyy2
    have hs4o : ∀ x, x ≠ y → x ≠ y2 → C4.st x = C3.st x := fun x h1 h2 =>
      Protocol.interact_st_other C3 h1 h2
    have hact4 : C4.active = C3.active \ SimpleGraph.edge y y2 := by
      rw [Protocol.interact_active_of_edge_false hdrop']
    refine ⟨C4, hR3.trans (Protocol.reachable_of_ne hyy2), inv_interact hk hI3 hyy2,
      μ_lt_iff.2 (.inr ⟨?_, .inl ?_⟩)⟩
    · rw [nTop_eq_zero hN, nTop_eq_zero (C := C4) (fun x => ?_)]
      by_cases h1 : x = y
      · rw [h1, hs4u]; rw [hy3, heq] at hiu4; omega
      by_cases h2 : x = y2
      · rw [h2, hs4v]; have := hN3 y2 (Ne.symm hyy2); omega
      rw [hs4o x h1 h2]
      exact hN3 x h1
    · have hc2 : ((G \ SimpleGraph.edge x1 x2) \ SimpleGraph.edge y y2).Reachable y y2 := by
        rw [sdiff_sdiff_comm]
        exact reachable_sdiff_edge_of_not_reachable
          (fun h => hsep x1 y hax1 hby (h.mono sdiff_le).symm)
          (fun h => hsep x2 y hax2 hby (h.mono sdiff_le).symm) hcyc2
      refine unreach_lt (fun p q h => ?_) (a := x1) (b := y) ?_ (hsep x1 y hax1 hby)
      · refine (reachable_sdiff_edge_of_reachable hc2 (hmono3 p q h)).mono ?_
        rw [hact4]
        exact sdiff_le_sdiff_right hle3
      · refine SimpleGraph.Adj.reachable ?_
        rw [hact4, SimpleGraph.sdiff_adj, SimpleGraph.edge_adj]
        refine ⟨hadj3, ?_⟩
        rintro ⟨⟨h, -⟩ | ⟨h, -⟩, -⟩
        · exact hx1y h
        · exact hy2x1 h.symm

/-- From every configuration satisfying `Inv`, the closed set `S` is reachable. -/
theorem reach_S (hn : k + 1 ≤ Fintype.card V) (C : Config V (St k)) (hC : Inv C) :
    ∃ D, (kRC k hk).Reachable C D ∧ D ∈ S k := by
  suffices key : ∀ C : Config V (St k), Inv C → C ∉ S k →
      ∃ D, (kRC k hk).Reachable C D ∧ Inv D ∧ μ D < μ C by
    obtain ⟨D, hR, -, hD⟩ :=
      exists_reach_of_measure (R := (kRC k hk).Step) Inv (· ∈ S k) μ key C hC
    exact ⟨D, hR, hD⟩
  intro C hI hnS
  by_cases hT : ∃ u, (C.st u).idx = k + 1
  · obtain ⟨u, hu⟩ := hT
    exact step_top hk hI hu
  have hN : NoTop C := fun x => by
    have := (C.st x).idx_le
    have := not_exists.1 hT x
    omega
  by_cases h1 : ∃ u w, u ≠ w ∧ (C.st u).isL = true ∧ (C.st w).isL = true ∧
      C.active.Reachable u w
  · obtain ⟨u, w, huw, hu, hw, hr⟩ := h1
    exact step_leaders hk hI hN huw hu hw hr
  by_cases h2 : ∃ u v, u ≠ v ∧ C.deg u < k ∧ C.deg v < k ∧ C.edge u v = false
  · obtain ⟨u, v, huv, hu, hv, he⟩ := h2
    exact step_activate hk hI hN huv hu hv he
  push Not at h1 h2
  have h2' : ∀ u v, u ≠ v → C.deg u < k → C.deg v < k → C.edge u v = true := fun u v huv hu hv =>
    by simpa using h2 u v huv hu hv
  have hdegk : ∀ x, C.deg x ≤ k := fun x => hI.1 x ▸ hN x
  have : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  by_cases h3 : C.active.Connected
  · exfalso
    apply hnS
    refine ⟨hI, hN, h3, ?_, h2'⟩
    obtain ⟨u, v, huv⟩ := exists_pair_ne V
    obtain ⟨p⟩ := h3.preconnected u v
    obtain ⟨ℓ, hℓ, -⟩ := hI.2 u (deg_pos_of_adj (p.adj_snd (p.not_nil_of_ne huv)))
    refine ⟨ℓ, fun x => ⟨fun hx => ?_, fun hx => hx ▸ hℓ⟩⟩
    by_contra hne
    exact h1 x ℓ hne hx hℓ (h3.preconnected x ℓ)
  · obtain ⟨a, b, hab⟩ : ∃ a b, ¬ C.active.Reachable a b := by
      by_contra h
      push Not at h
      exact h3 ⟨h⟩
    by_cases hXa : ∃ x, C.active.Reachable a x ∧ C.deg x < k
    · -- the component of `b` has no deficient agent
      obtain ⟨x, hax, hx⟩ := hXa
      refine step_merge hk hI hN (a := b) (b := a) (fun h => hab h.symm) (fun y hby => ?_)
      have : ¬ C.deg y < k := fun hy => by
        have hxy : x ≠ y := fun h => hab (hax.trans (h ▸ hby.symm))
        exact hab (hax.trans ((show C.active.Adj x y from ⟨hxy, h2' x y hxy hx hy⟩).reachable.trans
          hby.symm))
      have := hdegk y
      omega
    · push Not at hXa
      refine step_merge hk hI hN hab (fun x hx => ?_)
      have := hXa x hx
      have := hdegk x
      omega

/-- **Theorem 12** of Michail–Spirakis (PODC 2014). For every `k ≥ 2` and population size
`n ≥ k + 1`, Protocol 8 (kRC) constructs a connected spanning network in which at least
`n − k + 1` nodes have degree `k` and each of the remaining `l ≤ k − 1` nodes has degree at least
`l − 1` and at most `k − 1` (with the typo fix `l_0 := q_0` in the rule
`(l_{k+1}, l_1, 1) → (l_k, l_0, 0)`). -/
theorem kRC_constructs (hn : k + 1 ≤ Fintype.card V) :
    (kRC k hk).Constructs (V := V) (IsAlmostRegular k) :=
  (kRC k hk).constructs_of_reach (S k) (S_trap hk) (fun _ _ hC h => S_output hk hC h)
    (fun _ hC => S_almostRegular hk hn hC)
    (fun C hC => (reach_S hk hn C (inv_reach hk (inv_init hk) hC)).imp fun _ h => ⟨h.2, h.1⟩)

/-- Non-vacuity: the hypotheses of Theorem 12 are satisfiable for every `k ≥ 2`. -/
example (hk : 2 ≤ k) : (kRC k hk).Constructs (V := Fin (k + 1)) (IsAlmostRegular k) :=
  kRC_constructs hk (by simp)

end Podc.NetworkConstructors.KRC
