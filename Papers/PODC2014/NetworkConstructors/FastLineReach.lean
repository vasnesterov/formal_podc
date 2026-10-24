import Papers.PODC2014.NetworkConstructors.FastLine

/-!
# Protocol 3 (Fast-Global-Line) constructs a spanning line (Theorem 5, correctness)

From every configuration satisfying the invariant we first finish all pending merges
(`reach_noTrans`), and then repeat one of the following *rounds*, each of which decreases
`(#q₀, #awake tokens, n − #agents in awake lines)` lexicographically (`round`):
an awake leader absorbs an isolated `q₀` (rule 2) or `f₀` (rule 7); two `q₀` form a line (rule 1);
two awake leaders play their game (rules 3, 4/5, 6: the loser's line falls asleep); an awake leader
takes one agent from a sleeping line (rules 8, 4/5, 6). When no round applies, there is a unique
awake leader, no isolated agent and no sleeping line: the configuration is silent and its active
graph is a spanning line.
-/

namespace Podc.NetworkConstructors.FastLine

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem St

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No merge in progress. -/
def NoTrans (C : Config V St) : Prop := ∀ x, C.st x ≠ l' ∧ C.st x ≠ l'' ∧ C.st x ≠ q2'

/-- Counting agents whose state satisfies `p`. -/
def cnt (p : St → Prop) [DecidablePred p] (C : Config V St) : ℕ :=
  (Finset.univ.filter fun x => p (C.st x)).card

omit [DecidableEq V] in
/-- Counting states when the states change only on a finite set `S`. -/
theorem cnt_add [DecidableEq V] {C D : Config V St} (S : Finset V) (h : ∀ x ∉ S, D.st x = C.st x)
    (p : St → Prop) [DecidablePred p] :
    cnt p D + ∑ x ∈ S, (if p (C.st x) then 1 else 0) =
      cnt p C + ∑ x ∈ S, (if p (D.st x) then 1 else 0) := by
  simp only [cnt, Finset.card_filter]
  rw [← Finset.sum_add_sum_compl S, ← Finset.sum_add_sum_compl S (fun x => if p (C.st x) then 1 else 0)]
  have : ∑ x ∈ Sᶜ, (if p (D.st x) then 1 else 0) = ∑ x ∈ Sᶜ, (if p (C.st x) then 1 else 0) :=
    Finset.sum_congr rfl fun x hx => by rw [h x (Finset.mem_compl.1 hx)]
  rw [this]; ring

/-- Agents in awake lines. -/
def awR (C : Config V St) : Finset V :=
  Finset.univ.filter fun x => ∃ t, (C.st t).Aw ∧ C.active.Reachable x t

section

variable {C : Config V St}

theorem deg_ne_zero_of_adj {x y : V} (h : C.active.Adj x y) : C.deg y ≠ 0 := by
  rw [Config.deg, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  exact ⟨x, by simp [h.1, C.symm y x, h.2]⟩

/-- An agent of degree 2 has a neighbour different from any given agent. -/
theorem exists_adj_ne {x : V} (hx : C.deg x = 2) (z : V) : ∃ y, C.active.Adj x y ∧ y ≠ z := by
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.1 hx
  have ha : a ∈ Finset.univ.filter fun v => v ≠ x ∧ C.edge x v = true := hs ▸ by simp
  have hb : b ∈ Finset.univ.filter fun v => v ≠ x ∧ C.edge x v = true := hs ▸ by simp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_cases haz : a = z
  · exact ⟨b, ⟨Ne.symm hb.1, hb.2⟩, fun h => hab (haz.trans h.symm)⟩
  · exact ⟨a, ⟨Ne.symm ha.1, ha.2⟩, haz⟩

theorem edge_false_of_iso (hC : Inv C) {u v : V} (hvu : v ≠ u) (hu : (C.st u).dg = 0) :
    C.edge v u = false := by
  by_contra h
  exact deg_ne_zero_of_adj ⟨hvu, by simpa using h⟩ (by rw [← hC.dg, hu])

theorem edge_false_of_tok (hC : Inv C) {u v : V} (huv : u ≠ v) (hu : (C.st u).Tok)
    (hv : (C.st v).Tok) : C.edge u v = false := by
  by_contra h
  exact huv (hC.uniq u v hu hv (SimpleGraph.Adj.reachable ⟨huv, by simpa using h⟩))

/-- The neighbour of a fresh `l'` token (other than its `q₂'` mark) is a `q₁` or a `q₂`. -/
theorem nbr_of_l' (hC : Inv C) {v x z : V} (hv : C.st v = l') (hx : C.st x = q2')
    (hvx : C.active.Adj v x) (hvz : C.active.Adj v z) (hzx : z ≠ x) :
    C.st z = q1 ∨ C.st z = q2 := by
  have hzT : ¬ (C.st z).Tok := fun h =>
    hvz.ne (hC.uniq v z (by rw [hv]; decide) h hvz.reachable)
  have hzq : C.st z ≠ q2' := fun h =>
    hzx (hC.mark3 z x h hx (hvz.symm.reachable.trans hvx.reachable))
  have hd : (C.st z).dg ≠ 0 := by rw [hC.dg]; exact deg_ne_zero_of_adj hvz
  revert hzT hzq hd
  cases C.st z <;> simp [St.Tok, St.dg]

end

/-! ### Finishing pending merges -/

theorem reach_noTrans {C : Config V St} (hC : Inv C) :
    ∃ D, P.Reachable C D ∧ Inv D ∧ NoTrans D := by
  suffices h : ∀ D : Config V St, Inv D → ¬ NoTrans D → ∃ E, P.Reachable D E ∧ Inv E ∧
      2 * cnt (· = l') E + cnt (· = l'') E < 2 * cnt (· = l') D + cnt (· = l'') D by
    exact exists_reach_of_measure (R := P.Step) Inv NoTrans
      (fun D => 2 * cnt (· = l') D + cnt (· = l'') D) h C hC
  intro D hD hnt
  have step : ∀ x y, x ≠ y → ∀ a b e, δ (D.st x) (D.st y) (D.edge x y) = (a, b, e) →
      (if D.st x = l' then 2 else 0) + (if D.st x = l'' then 1 else 0) +
        ((if D.st y = l' then 2 else 0) + (if D.st y = l'' then 1 else 0)) >
      (if a = l' then 2 else 0) + (if a = l'' then 1 else 0) +
        ((if b = l' then 2 else 0) + (if b = l'' then 1 else 0)) →
      ∃ E, P.Reachable D E ∧ Inv E ∧
        2 * cnt (· = l') E + cnt (· = l'') E < 2 * cnt (· = l') D + cnt (· = l'') D := by
    intro x y hxy a b e hδ hlt
    obtain ⟨hEx, hEy, hEo⟩ := interact_states hxy hδ
    refine ⟨P.interact D x y, Protocol.reachable_of_ne hxy, inv_step hD (Protocol.step_of_ne hxy),
      ?_⟩
    have h1 := cnt_add {x, y} (fun z hz => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
      exact hEo z hz.1 hz.2) (· = l') (C := D)
    have h2 := cnt_add {x, y} (fun z hz => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
      exact hEo z hz.1 hz.2) (· = l'') (C := D)
    rw [Finset.sum_pair hxy, Finset.sum_pair hxy, hEx, hEy] at h1 h2
    split_ifs at hlt h1 h2 <;> omega
  simp only [NoTrans, not_forall] at hnt
  obtain ⟨v, hv⟩ := hnt
  by_cases hv1 : D.st v = l'
  · obtain ⟨x, hvx, hx⟩ := hD.mark1 v (by rw [hv1]; decide)
    obtain ⟨z, hvz, hzx⟩ := exists_adj_ne (by rw [← hD.dg, hv1]; rfl) x
    rcases nbr_of_l' hD hv1 hx hvx hvz hzx with hz | hz
    · exact step v z hvz.1 l'' f0 false (by rw [hv1, hz, hvz.2]; rfl)
        (by rw [hv1, hz]; simp)
    · exact step v z hvz.1 l'' f1 false (by rw [hv1, hz, hvz.2]; rfl)
        (by rw [hv1, hz]; simp)
  by_cases hv2 : D.st v = l''
  · obtain ⟨x, hvx, hx⟩ := hD.mark1 v (by rw [hv2]; decide)
    exact step v x hvx.1 l q2 true (by rw [hv2, hx, hvx.2]; rfl) (by rw [hv2, hx]; simp)
  · have hv3 : D.st v = q2' := by tauto
    obtain ⟨y, hvy, hy⟩ := hD.mark2 v hv3
    by_cases hy1 : D.st y = l'
    · obtain ⟨x, hyx, hx⟩ := hD.mark1 y hy
      obtain ⟨z, hyz, hzx⟩ := exists_adj_ne (by rw [← hD.dg, hy1]; rfl) x
      rcases nbr_of_l' hD hy1 hx hyx hyz hzx with hz | hz
      · exact step y z hyz.1 l'' f0 false (by rw [hy1, hz, hyz.2]; rfl) (by rw [hy1, hz]; simp)
      · exact step y z hyz.1 l'' f1 false (by rw [hy1, hz, hyz.2]; rfl) (by rw [hy1, hz]; simp)
    · have hy2 : D.st y = l'' := hy.resolve_left hy1
      exact step y v hvy.symm.1 l q2 true (by rw [hy2, hv3, D.symm, hvy.2]; rfl)
        (by rw [hy2, hv3]; simp)

/-! ### A complete merge: rules 3 or 8, then 4 or 5, then 6 -/

/-- The awake leader at `u` wins against the token at `v` (an awake leader or the `f₁` end of a
sleeping line): `u` becomes internal, `v` becomes the new endpoint leader, and `v`'s old
neighbour `z` becomes the `f₁` end of the rest of `v`'s line (or an isolated `f₀`). -/
theorem merge {C : Config V St} (hC : Inv C) (hN : NoTrans C) {u v : V} (huv : u ≠ v)
    (hu : C.st u = l) (hv : C.st v = l ∨ C.st v = f1) :
    ∃ D z, P.Reachable C D ∧ Inv D ∧ NoTrans D ∧ z ≠ u ∧ z ≠ v ∧ C.active.Adj v z ∧
      D.st u = q2 ∧ D.st v = l ∧ ((D.st z = f1 ∧ C.st z = q2) ∨ (D.st z = f0 ∧ C.st z = q1)) ∧
      (∀ x, x ≠ u → x ≠ v → x ≠ z → D.st x = C.st x) ∧
      D.active = (C.active ⊔ SimpleGraph.edge u v) \ SimpleGraph.edge v z := by
  have huT : (C.st u).Tok := by rw [hu]; decide
  have hvT : (C.st v).Tok := by rcases hv with h | h <;> rw [h] <;> decide
  have he : C.edge u v = false := edge_false_of_tok hC huv huT hvT
  -- step 1: rule 3 or 8
  have hδ1 : δ (C.st u) (C.st v) (C.edge u v) = (q2', l', true) := by
    rcases hv with h | h <;> rw [hu, h, he] <;> rfl
  set C1 := P.interact C u v with hC1
  obtain ⟨h1u, h1v, h1o⟩ := interact_states huv hδ1
  have hI1 : Inv C1 := inv_step hC (Protocol.step_of_ne huv)
  have hG1 : C1.active = C.active ⊔ SimpleGraph.edge u v :=
    Protocol.interact_active_of_edge_true huv (by show (δ _ _ _).2.2 = _; rw [hδ1])
  have hadj1 : C1.active.Adj v u := by
    rw [hG1]; exact (SimpleGraph.sup_adj _ _ _ _).2 (.inr ((SimpleGraph.edge_adj _ _ _ _).2
      ⟨.inr ⟨rfl, rfl⟩, Ne.symm huv⟩))
  obtain ⟨z, hvz1, hzu⟩ := exists_adj_ne (C := C1) (by rw [← hI1.dg, h1v]; rfl) u
  have hzv : z ≠ v := hvz1.ne.symm
  have hvz : C.active.Adj v z := by
    rw [hG1, SimpleGraph.sup_adj, SimpleGraph.edge_adj] at hvz1
    rcases hvz1 with h | ⟨h, -⟩
    · exact h
    · rcases h with ⟨rfl, rfl⟩ | ⟨-, rfl⟩
      · exact absurd rfl huv
      · exact absurd rfl hzu
  have hz1 : C1.st z = C.st z := h1o z hzu hzv
  have hzst := nbr_of_l' hI1 h1v h1u hadj1 hvz1 hzu
  rw [hz1] at hzst
  -- step 2: rule 4 or 5
  have he2 : C1.edge v z = true := hvz1.2
  obtain ⟨b, hb, hδ2⟩ : ∃ b, ((b = f1 ∧ C.st z = q2) ∨ (b = f0 ∧ C.st z = q1)) ∧
      δ (C1.st v) (C1.st z) (C1.edge v z) = (l'', b, false) := by
    rcases hzst with h | h
    · exact ⟨f0, .inr ⟨rfl, h⟩, by rw [h1v, hz1, h, he2]; rfl⟩
    · exact ⟨f1, .inl ⟨rfl, h⟩, by rw [h1v, hz1, h, he2]; rfl⟩
  set C2 := P.interact C1 v z with hC2
  obtain ⟨h2v, h2z, h2o⟩ := interact_states hzv.symm hδ2
  have hI2 : Inv C2 := inv_step hI1 (Protocol.step_of_ne hzv.symm)
  have hG2 : C2.active = C1.active \ SimpleGraph.edge v z :=
    Protocol.interact_active_of_edge_false (by show (δ _ _ _).2.2 = _; rw [hδ2])
  -- step 3: rule 6
  have he3 : C2.edge v u = true := by
    rw [hC2, Protocol.interact_edge_other C1 (by
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact hzu h.symm
      · exact hzv.symm h)]
    exact hadj1.2
  have h2u : C2.st u = q2' := (h2o u (Ne.symm huv.symm) hzu.symm).trans h1u
  have hδ3 : δ (C2.st v) (C2.st u) (C2.edge v u) = (l, q2, true) := by
    rw [h2v, h2u, he3]; rfl
  obtain ⟨h3v, h3u, h3o⟩ := interact_states huv.symm hδ3
  have hG3 : (P.interact C2 v u).active = C2.active :=
    Protocol.interact_active_of_edge_eq (by show (δ _ _ _).2.2 = _; rw [hδ3, he3])
  refine ⟨P.interact C2 v u, z,
    ((Protocol.reachable_of_ne huv).tail (Protocol.step_of_ne hzv.symm)).tail
      (Protocol.step_of_ne huv.symm),
    inv_step hI2 (Protocol.step_of_ne huv.symm), fun x => ?_, hzu, hzv, hvz, h3u, h3v, ?_, ?_, ?_⟩
  · by_cases hxu : x = u
    · rw [hxu, h3u]; decide
    by_cases hxv : x = v
    · rw [hxv, h3v]; decide
    rw [h3o x hxv hxu]
    by_cases hxz : x = z
    · rw [hxz, h2z]; rcases hb with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
    rw [h2o x hxv hxz, h1o x hxu hxv]; exact hN x
  · rw [h3o z hzv hzu, h2z]
    rcases hb with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact .inl ⟨rfl, h⟩
    · exact .inr ⟨rfl, h⟩
  · intro x hxu hxv hxz
    rw [h3o x hxv hxu, h2o x hxv hxz, h1o x hxu hxv]
  · rw [hG3, hG2, hG1]

/-! ### Rounds -/

/-- The construction is finished: no isolated agent, no sleeping line, one awake leader. -/
def Done (C : Config V St) : Prop :=
  (∀ x, C.st x ≠ q0 ∧ C.st x ≠ f0 ∧ C.st x ≠ f1) ∧ ∀ x y, (C.st x).Aw → (C.st y).Aw → x = y

/-- The measure of progress. -/
def μ (C : Config V St) : ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (cnt (· = q0) C, toLex (cnt St.Aw C, Fintype.card V - (awR C).card))

theorem mem_awR {C : Config V St} {x : V} :
    x ∈ awR C ↔ ∃ t, (C.st t).Aw ∧ C.active.Reachable x t := by
  simp [awR]

theorem awR_card_lt {C D : Config V St} {v : V} (hsub : ∀ x ∈ awR C, x ∈ awR D)
    (hv : v ∈ awR D) (hv' : v ∉ awR C) : Fintype.card V - (awR D).card <
      Fintype.card V - (awR C).card := by
  have h1 : (awR C).card < (awR D).card :=
    Finset.card_lt_card ⟨hsub, fun h => hv' (h hv)⟩
  have h2 : (awR D).card ≤ Fintype.card V := Finset.card_le_univ _
  omega

theorem round (hn : 2 ≤ Fintype.card V) {C : Config V St} (hC : Inv C) (hN : NoTrans C)
    (hnd : ¬ Done C) : ∃ D, P.Reachable C D ∧ (Inv D ∧ NoTrans D) ∧ μ D < μ C := by
  have hAwl : ∀ x, (C.st x).Aw → C.st x = l := fun x hx => by
    rcases hx with h | h | h
    · exact h
    · exact absurd h (hN x).1
    · exact absurd h (hN x).2.1
  -- a single activation step `(u, v)` with new states `(a, b)`
  have single : ∀ u v, u ≠ v → ∀ a b, δ (C.st u) (C.st v) (C.edge u v) = (a, b, true) →
      a ≠ l' ∧ a ≠ l'' ∧ a ≠ q2' → b ≠ l' ∧ b ≠ l'' ∧ b ≠ q2' →
      P.Reachable C (P.interact C u v) ∧ (Inv (P.interact C u v) ∧ NoTrans (P.interact C u v)) := by
    intro u v huv a b hδ ha hb
    obtain ⟨hDu, hDv, hDo⟩ := interact_states huv hδ
    refine ⟨Protocol.reachable_of_ne huv, inv_step hC (Protocol.step_of_ne huv), fun x => ?_⟩
    by_cases hxu : x = u
    · rw [hxu, hDu]; exact ha
    by_cases hxv : x = v
    · rw [hxv, hDv]; exact hb
    rw [hDo x hxu hxv]; exact hN x
  have pair : ∀ (p : St → Prop) [DecidablePred p] u v, u ≠ v → ∀ a b, δ (C.st u) (C.st v)
      (C.edge u v) = (a, b, true) → cnt p (P.interact C u v) + ((if p (C.st u) then 1 else 0) +
        (if p (C.st v) then 1 else 0)) = cnt p C + ((if p a then 1 else 0) + (if p b then 1 else 0)) := by
    intro p _ u v huv a b hδ
    obtain ⟨hDu, hDv, hDo⟩ := interact_states huv hδ
    have := cnt_add {u, v} (fun z hz => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
      exact hDo z hz.1 hz.2) p (C := C) (D := P.interact C u v)
    rwa [Finset.sum_pair huv, Finset.sum_pair huv, hDu, hDv] at this
  have triple : ∀ (p : St → Prop) [DecidablePred p] (D : Config V St) u v z, u ≠ v → z ≠ u →
      z ≠ v → (∀ x, x ≠ u → x ≠ v → x ≠ z → D.st x = C.st x) →
      cnt p D + ((if p (C.st u) then 1 else 0) + ((if p (C.st v) then 1 else 0) +
        (if p (C.st z) then 1 else 0))) = cnt p C + ((if p (D.st u) then 1 else 0) +
        ((if p (D.st v) then 1 else 0) + (if p (D.st z) then 1 else 0))) := by
    intro p _ D u v z huv hzu hzv hD
    have := cnt_add {u, v, z} (fun x hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      exact hD x hx.1 hx.2.1 hx.2.2) p (C := C) (D := D)
    rwa [Finset.sum_insert (by simp [huv, hzu.symm]), Finset.sum_pair hzv.symm,
      Finset.sum_insert (by simp [huv, hzu.symm]), Finset.sum_pair hzv.symm] at this
  by_cases hq : ∃ v, C.st v = q0
  · obtain ⟨v, hv⟩ := hq
    by_cases hl : ∃ u, C.st u = l
    · -- (a) rule 2
      obtain ⟨u, hu⟩ := hl
      have huv : u ≠ v := by rintro rfl; rw [hu] at hv; exact absurd hv (by decide)
      have hδ : δ (C.st u) (C.st v) (C.edge u v) = (q2, l, true) := by
        rw [hu, hv, edge_false_of_iso hC huv (by rw [hv]; rfl)]; rfl
      obtain ⟨hr, hI⟩ := single u v huv q2 l hδ (by decide) (by decide)
      refine ⟨_, hr, hI, Prod.Lex.toLex_lt_toLex.2 (.inl ?_)⟩
      have := pair (· = q0) u v huv q2 l hδ
      rw [hu, hv] at this; simp at this; omega
    · -- (b) rule 1
      push Not at hl
      obtain ⟨w, hwv⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
      have hw : C.st w = q0 := by
        by_contra hw
        obtain ⟨t, ht⟩ := hC.awake ⟨w, hw⟩
        exact hl t (hAwl t ht)
      have hδ : δ (C.st v) (C.st w) (C.edge v w) = (q1, l, true) := by
        rw [hv, hw, edge_false_of_iso hC (Ne.symm hwv) (by rw [hw]; rfl)]; rfl
      obtain ⟨hr, hI⟩ := single v w (Ne.symm hwv) q1 l hδ (by decide) (by decide)
      refine ⟨_, hr, hI, Prod.Lex.toLex_lt_toLex.2 (.inl ?_)⟩
      have := pair (· = q0) v w (Ne.symm hwv) q1 l hδ
      rw [hv, hw] at this; simp at this; omega
  push Not at hq
  have hex : ∃ t, C.st t = l := by
    obtain ⟨a⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨t, ht⟩ := hC.awake ⟨a, hq a⟩
    exact ⟨t, hAwl t ht⟩
  obtain ⟨u, hu⟩ := hex
  have hsame : ∀ D : Config V St, cnt (· = q0) D = cnt (· = q0) C → cnt St.Aw D = cnt St.Aw C →
      Fintype.card V - (awR D).card < Fintype.card V - (awR C).card → μ D < μ C := by
    intro D h1 h2 h3
    exact Prod.Lex.toLex_lt_toLex.2 (.inr ⟨h1, Prod.Lex.toLex_lt_toLex.2 (.inr ⟨h2, h3⟩)⟩)
  by_cases hf0 : ∃ v, C.st v = f0
  · -- (c) rule 7
    obtain ⟨v, hv⟩ := hf0
    have huv : u ≠ v := by rintro rfl; rw [hu] at hv; exact absurd hv (by decide)
    have hv0 : C.deg v = 0 := by rw [← hC.dg, hv]; rfl
    have hδ : δ (C.st u) (C.st v) (C.edge u v) = (q2, l, true) := by
      rw [hu, hv, edge_false_of_iso hC huv (by rw [hv]; rfl)]; rfl
    obtain ⟨hr, hI⟩ := single u v huv q2 l hδ (by decide) (by decide)
    obtain ⟨hDu, hDv, hDo⟩ := interact_states huv hδ
    have hG : (P.interact C u v).active = C.active ⊔ SimpleGraph.edge u v :=
      Protocol.interact_active_of_edge_true huv (by show (δ _ _ _).2.2 = _; rw [hδ])
    have hle : C.active ≤ (P.interact C u v).active := hG ▸ le_sup_left
    have hadj : (P.interact C u v).active.Adj u v := by
      rw [hG]; exact (SimpleGraph.sup_adj _ _ _ _).2 (.inr ((SimpleGraph.edge_adj _ _ _ _).2
        ⟨.inl ⟨rfl, rfl⟩, huv⟩))
    refine ⟨_, hr, hI, hsame _ ?_ ?_ (awR_card_lt (v := v) ?_ ?_ ?_)⟩
    · have := pair (· = q0) u v huv q2 l hδ
      rw [hu, hv] at this; simp at this; omega
    · have := pair St.Aw u v huv q2 l hδ
      rw [hu, hv] at this; simp [St.Aw] at this; omega
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := mem_awR.1 hx
      have htv : t ≠ v := by rintro rfl; rw [hv] at ht; exact absurd ht (by decide)
      refine mem_awR.2 ?_
      by_cases htu : t = u
      · subst htu; exact ⟨v, by rw [hDv]; decide, (hxt.mono hle).trans hadj.reachable⟩
      · exact ⟨t, by rw [hDo t htu htv]; exact ht, hxt.mono hle⟩
    · exact mem_awR.2 ⟨v, by rw [hDv]; decide, .rfl⟩
    · intro hx
      obtain ⟨t, ht, hvt⟩ := mem_awR.1 hx
      have := eq_of_reachable_deg_zero hv0 hvt.symm
      subst this; rw [hv] at ht; exact absurd ht (by decide)
  push Not at hf0
  by_cases hf1 : ∃ v, C.st v = f1
  · -- (e) rules 8, 4/5, 6
    obtain ⟨v, hv⟩ := hf1
    have huv : u ≠ v := by rintro rfl; rw [hu] at hv; exact absurd hv (by decide)
    obtain ⟨D, z, hr, hI, hND, hzu, hzv, hvz, hDu, hDv, hDz, hDo, hG⟩ :=
      merge hC hN huv hu (.inr hv)
    refine ⟨D, hr, ⟨hI, hND⟩, hsame _ ?_ ?_ (awR_card_lt (v := v) ?_ ?_ ?_)⟩
    · have := triple (· = q0) D u v z huv hzu hzv hDo
      rw [hu, hv, hDu, hDv] at this
      rcases hDz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at this <;> simp at this <;> omega
    · have := triple St.Aw D u v z huv hzu hzv hDo
      rw [hu, hv, hDu, hDv] at this
      rcases hDz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at this <;> simp [St.Aw] at this <;>
        omega
    · intro x hx
      obtain ⟨t, ht, hxt⟩ := mem_awR.1 hx
      have htT : (C.st t).Tok := St.tok_of_aw ht
      have hvT : (C.st v).Tok := by rw [hv]; decide
      have htv : ¬ C.active.Reachable t v := fun h => by
        have := hC.uniq t v htT hvT h
        subst this; rw [hv] at ht; exact absurd ht (by decide)
      have hxt' : (C.active \ SimpleGraph.edge v z).Reachable x t := by
        rcases hxt.sdiff_edge (u := v) (v := z) with h | h | h
        · exact h
        · exact absurd (hxt.symm.trans (h.mono sdiff_le)) htv
        · exact absurd (hxt.symm.trans ((h.mono sdiff_le).trans hvz.symm.reachable)) htv
      have hle : C.active \ SimpleGraph.edge v z ≤ D.active := by
        rw [hG]; exact sdiff_le_sdiff_right le_sup_left
      refine mem_awR.2 ?_
      by_cases htu : t = u
      · subst htu
        have hadj : D.active.Adj t v := by
          rw [hG, SimpleGraph.sdiff_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj,
            SimpleGraph.edge_adj]
          refine ⟨.inr ⟨.inl ⟨rfl, rfl⟩, huv⟩, fun h => ?_⟩
          rcases h.1 with ⟨h, -⟩ | ⟨h, -⟩
          · exact huv h
          · exact hzu h.symm
        exact ⟨v, by rw [hDv]; decide, (hxt'.mono hle).trans hadj.reachable⟩
      · have htv' : t ≠ v := by rintro rfl; rw [hv] at ht; exact absurd ht (by decide)
        have htz : t ≠ z := by
          rintro rfl
          rcases hDz with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at ht <;> exact absurd ht (by decide)
        exact ⟨t, by rw [hDo t htu htv' htz]; exact ht, hxt'.mono hle⟩
    · exact mem_awR.2 ⟨v, by rw [hDv]; decide, .rfl⟩
    · intro hx
      obtain ⟨t, ht, hvt⟩ := mem_awR.1 hx
      have := hC.uniq v t (by rw [hv]; decide) (St.tok_of_aw ht) hvt
      subst this; rw [hv] at ht; exact absurd ht (by decide)
  push Not at hf1
  -- (d) two awake leaders: rules 3, 4/5, 6
  have : ¬ ∀ x y, (C.st x).Aw → (C.st y).Aw → x = y := fun h =>
    hnd ⟨fun x => ⟨hq x, hf0 x, hf1 x⟩, h⟩
  push Not at this
  obtain ⟨a, b, ha, hb, hab⟩ := this
  obtain ⟨D, z, hr, hI, hND, hzu, hzv, -, hDu, hDv, hDz, hDo, -⟩ :=
    merge hC hN hab (hAwl a ha) (.inl (hAwl b hb))
  refine ⟨D, hr, ⟨hI, hND⟩, Prod.Lex.toLex_lt_toLex.2 (.inr ⟨?_,
    Prod.Lex.toLex_lt_toLex.2 (.inl ?_)⟩)⟩
  · have := triple (· = q0) D a b z hab hzu hzv hDo
    rw [hAwl a ha, hAwl b hb, hDu, hDv] at this
    rcases hDz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at this <;> simp at this <;> omega
  · have := triple St.Aw D a b z hab hzu hzv hDo
    rw [hAwl a ha, hAwl b hb, hDu, hDv] at this
    rcases hDz with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at this <;> simp [St.Aw] at this <;> omega

/-! ### Final configurations -/

omit [Fintype V] in
/-- Finished configurations are silent. -/
theorem done_silent {C : Config V St} (hN : NoTrans C) (hD : Done C) {u v : V} (huv : u ≠ v) :
    P.interact C u v = C := by
  apply Protocol.interact_eq_self
  obtain ⟨h0, h1⟩ := hD
  show δ _ _ _ = _
  rcases δ_cases (C.st u) (C.st v) (C.edge u v) with h | ⟨hu, -⟩ | ⟨-, hv, -⟩ | ⟨hu, hv, -⟩ |
    ⟨hu, -⟩ | ⟨hu, -⟩ | ⟨hu, -⟩ | ⟨-, hv, -⟩ | ⟨-, hv, -⟩
  · exact h
  · exact absurd hu (h0 u).1
  · exact absurd hv (h0 v).1
  · exact absurd (h1 u v (by rw [hu]; decide) (by rw [hv]; decide)) huv
  · exact absurd hu (hN u).1
  · exact absurd hu (hN u).1
  · exact absurd hu (hN u).2.1
  · exact absurd hv (h0 v).2.1
  · exact absurd hv (h0 v).2.2

theorem done_step {C D : Config V St} (hN : NoTrans C) (hD : Done C) (h : P.Step C D) :
    D = C := by
  obtain ⟨u, v, huv, rfl⟩ := h
  exact done_silent hN hD huv

theorem done_spanningLine {C : Config V St} (hC : Inv C) (hN : NoTrans C) (hD : Done C)
    [Nonempty V] : IsSpanningLine (P.output C) := by
  obtain ⟨h0, h1⟩ := hD
  have hdeg : ∀ v, C.deg v ≠ 0 := fun v => by
    rw [← hC.dg]; have := h0 v; cases h : C.st v <;> simp_all [St.dg]
  have htok : ∀ x, (C.st x).Tok → (C.st x).Aw := fun x hx => by
    rcases hx with h | h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
    · exact absurd h (h0 x).2.2
  obtain ⟨x₀, hx₀, -⟩ := hC.cover (Classical.arbitrary V) (hdeg _)
  have hconn : C.active.Connected := by
    refine SimpleGraph.connected_iff_exists_forall_reachable _ |>.2 ⟨x₀, fun v => ?_⟩
    obtain ⟨y, hy, hvy⟩ := hC.cover v (hdeg v)
    rw [h1 y x₀ (htok y hy) (htok x₀ hx₀)] at hvy
    exact hvy.symm
  refine isSpanningLine_output (fun _ => rfl) hconn hC.acyclic fun v => ?_
  rw [← hC.dg]; have := h0 v; have := hN v; cases h : C.st v <;> simp_all [St.dg]

/-- **Theorem 5 (correctness) of Michail–Spirakis.** For every number `n ≥ 2` of agents, Protocol
Fast-Global-Line constructs a spanning line under every globally fair scheduler. -/
theorem constructs_spanningLine (hn : 2 ≤ Fintype.card V) :
    P.Constructs (V := V) IsSpanningLine := by
  have : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  refine P.constructs_of_reach {C | Inv C ∧ NoTrans C ∧ Done C}
    (fun C D hC hCD => by rw [Set.mem_ofPred_eq, done_step hC.2.1 hC.2.2 hCD]; exact hC)
    (fun C D hC hCD => by rw [done_step hC.2.1 hC.2.2 hCD])
    (fun C hC => done_spanningLine hC.1 hC.2.1 hC.2.2) (fun C hC => ?_)
  obtain ⟨D, hCD, hD, hDN⟩ := reach_noTrans (inv_reach inv_init hC)
  obtain ⟨E, hDE, ⟨hE, hEN⟩, hEd⟩ := exists_reach_of_measure (R := P.Step)
    (fun D => Inv D ∧ NoTrans D) Done μ (fun D hD hnd => round hn hD.1 hD.2 hnd) D ⟨hD, hDN⟩
  exact ⟨E, ⟨hE, hEN, hEd⟩, hCD.trans hDE⟩

end Podc.NetworkConstructors.FastLine
