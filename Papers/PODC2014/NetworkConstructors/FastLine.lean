import Papers.PODC2014.NetworkConstructors.Problems

/-!
# Protocol 3 (Fast-Global-Line): the invariant

States `q₀, q₁, q₂, q₂', l, l', l'', f₀, f₁`; rules
1. `(q₀, q₀, 0) → (q₁, l, 1)`
2. `(l, q₀, 0) → (q₂, l, 1)`
3. `(l, l, 0) → (q₂', l', 1)`
4. `(l', q₂, 1) → (l'', f₁, 0)`
5. `(l', q₁, 1) → (l'', f₀, 0)`
6. `(l'', q₂', 1) → (l, q₂, 1)`
7. `(l, f₀, 0) → (q₂, l, 1)`
8. `(l, f₁, 0) → (q₂', l', 1)`

Invariant (`Inv`): the active graph is a forest of paths (acyclic; the degree is determined by the
state), every non-trivial component contains exactly one *token* (`l`, `l'`, `l''` for awake lines,
`f₁` for sleeping lines), the marked node `q₂'` sits next to the `l'`/`l''` token of its component
(at most one per component), and once some agent has left `q₀` there is an awake token.
-/

namespace Podc.NetworkConstructors.FastLine

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem

/-- States of Protocol 3 (Fast-Global-Line). -/
inductive St | q0 | q1 | q2 | q2' | l | l' | l'' | f0 | f1
  deriving DecidableEq, Repr

open St

instance : Fintype St :=
  ⟨{q0, q1, q2, q2', l, l', l'', f0, f1}, fun x => by cases x <;> simp⟩

/-- The degree of an agent in a given state. -/
def St.dg : St → ℕ
  | q0 => 0
  | f0 => 0
  | q1 => 1
  | l => 1
  | l'' => 1
  | f1 => 1
  | q2 => 2
  | q2' => 2
  | l' => 2

/-- Token states: one per non-trivial component. -/
def St.Tok (s : St) : Prop := s = l ∨ s = l' ∨ s = l'' ∨ s = f1

/-- Awake tokens. -/
def St.Aw (s : St) : Prop := s = l ∨ s = l' ∨ s = l''

/-- Tokens in the middle of a merge (they have a `q₂'` neighbour). -/
def St.Mk (s : St) : Prop := s = l' ∨ s = l''

instance : DecidablePred St.Tok := fun s => by unfold St.Tok; infer_instance
instance : DecidablePred St.Aw := fun s => by unfold St.Aw; infer_instance
instance : DecidablePred St.Mk := fun s => by unfold St.Mk; infer_instance

/-- The transition function of Protocol 3; unlisted triples are ineffective. -/
def δ : St → St → Bool → St × St × Bool
  | q0, q0, false => (q1, l, true)
  | l, q0, false => (q2, l, true)
  | l, l, false => (q2', l', true)
  | l', q2, true => (l'', f1, false)
  | l', q1, true => (l'', f0, false)
  | l'', q2', true => (l, q2, true)
  | l, f0, false => (q2, l, true)
  | l, f1, false => (q2', l', true)
  | a, b, e => (a, b, e)

/-- Protocol 3 (Fast-Global-Line): initial state `q₀`, all states are output states. -/
def P : Protocol St where
  init := q0
  out _ := true
  δ := δ

/-- The effective rules. -/
theorem δ_cases (a b : St) (e : Bool) :
    δ a b e = (a, b, e) ∨
    (a = q0 ∧ b = q0 ∧ e = false ∧ δ a b e = (q1, l, true)) ∨
    (a = l ∧ b = q0 ∧ e = false ∧ δ a b e = (q2, l, true)) ∨
    (a = l ∧ b = l ∧ e = false ∧ δ a b e = (q2', l', true)) ∨
    (a = l' ∧ b = q2 ∧ e = true ∧ δ a b e = (l'', f1, false)) ∨
    (a = l' ∧ b = q1 ∧ e = true ∧ δ a b e = (l'', f0, false)) ∨
    (a = l'' ∧ b = q2' ∧ e = true ∧ δ a b e = (l, q2, true)) ∨
    (a = l ∧ b = f0 ∧ e = false ∧ δ a b e = (q2, l, true)) ∨
    (a = l ∧ b = f1 ∧ e = false ∧ δ a b e = (q2', l', true)) := by
  cases a <;> cases b <;> cases e <;> simp [δ]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The inductive invariant. -/
structure Inv (C : Config V St) : Prop where
  dg : ∀ u, (C.st u).dg = C.deg u
  acyclic : C.active.IsAcyclic
  cover : ∀ u, C.deg u ≠ 0 → ∃ x, (C.st x).Tok ∧ C.active.Reachable u x
  uniq : ∀ x y, (C.st x).Tok → (C.st y).Tok → C.active.Reachable x y → x = y
  mark1 : ∀ y, (C.st y).Mk → ∃ x, C.active.Adj y x ∧ C.st x = q2'
  mark2 : ∀ x, C.st x = q2' → ∃ y, C.active.Adj x y ∧ (C.st y).Mk
  mark3 : ∀ x y, C.st x = q2' → C.st y = q2' → C.active.Reachable x y → x = y
  awake : (∃ u, C.st u ≠ q0) → ∃ t, (C.st t).Aw

theorem St.tok_of_mk {s : St} (h : s.Mk) : s.Tok := by
  rcases h with rfl | rfl <;> simp [St.Tok]

theorem St.tok_of_aw {s : St} (h : s.Aw) : s.Tok := by
  rcases h with rfl | rfl | rfl <;> simp [St.Tok]

/-- An agent of degree 0 is reachable only from itself. -/
theorem eq_of_reachable_deg_zero {C : Config V St} {x u : V} (hu : C.deg u = 0)
    (h : C.active.Reachable x u) : x = u := by
  obtain ⟨p⟩ := h.symm
  cases p with
  | nil => rfl
  | cons hadj _ =>
    exfalso
    rw [Config.deg_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree,
      Finset.card_eq_zero] at hu
    have : _ ∈ C.active.neighborFinset u := (SimpleGraph.mem_neighborFinset _ _ _).2 hadj
    rw [hu] at this
    simp at this

/-- The token of the component of a `q₂'` agent is an `l'`/`l''`. -/
theorem mk_of_reach_q2' {C : Config V St} (hC : Inv C) {x t : V} (hx : C.st x = q2')
    (ht : (C.st t).Tok) (h : C.active.Reachable x t) : (C.st t).Mk := by
  obtain ⟨y, hxy, hy⟩ := hC.mark2 x hx
  rw [hC.uniq t y ht (St.tok_of_mk hy) (h.symm.trans hxy.reachable)]
  exact hy

/-- A `q₂'` agent is not connected to an agent `u` that is isolated or a token other than
`l'`/`l''`. -/
theorem not_reach_q2' {C : Config V St} (hC : Inv C) {x u : V} (hx : C.st x = q2')
    (hu : C.deg u = 0 ∨ ((C.st u).Tok ∧ ¬ (C.st u).Mk)) : ¬ C.active.Reachable x u := by
  intro h
  rcases hu with hu | ⟨ht, hm⟩
  · have := eq_of_reachable_deg_zero hu h
    subst this
    rw [← hC.dg, hx] at hu
    exact absurd hu (by decide)
  · exact hm (mk_of_reach_q2' hC hx ht h)

theorem inv_init : Inv (P.initConfig : Config V St) where
  dg u := by simp [Protocol.initConfig, Config.deg, St.dg, P]
  acyclic := by
    have : (P.initConfig : Config V St).active = ⊥ := by
      ext u v; simp [Protocol.initConfig, Config.active_adj]
    rw [this]; exact SimpleGraph.isAcyclic_bot
  cover u h := absurd (by simp [Protocol.initConfig, Config.deg]) h
  uniq x _ hx := by simp [Protocol.initConfig, P, St.Tok] at hx
  mark1 y hy := by simp [Protocol.initConfig, P, St.Mk] at hy
  mark2 x hx := by simp [Protocol.initConfig, P] at hx
  mark3 x _ hx := by simp [Protocol.initConfig, P] at hx
  awake h := by simp [Protocol.initConfig, P] at h

section step

variable {C : Config V St} {u v : V}

omit [Fintype V] in
theorem interact_st_eq (C : Config V St) (u v x : V) :
    (P.interact C u v).st x = if x = u then (δ (C.st u) (C.st v) (C.edge u v)).1
      else if x = v then (δ (C.st u) (C.st v) (C.edge u v)).2.1 else C.st x := rfl

omit [Fintype V] in
/-- The states after an interaction. -/
theorem interact_states (huv : u ≠ v) {a b : St} {e : Bool}
    (hδ : δ (C.st u) (C.st v) (C.edge u v) = (a, b, e)) :
    (P.interact C u v).st u = a ∧ (P.interact C u v).st v = b ∧
      ∀ z, z ≠ u → z ≠ v → (P.interact C u v).st z = C.st z :=
  ⟨by rw [interact_st_eq, ite_eq_left rfl, hδ],
   by rw [interact_st_eq, ite_eq_right (Ne.symm huv), ite_eq_left rfl, hδ],
   fun z hzx hzy => Protocol.interact_st_other C hzx hzy⟩

/-- Preservation of the invariant by an activation joining two components (rules 1, 2, 3, 7,
8): `u` stops being a token, `v` becomes (or stays) an awake token. -/
theorem inv_activate (hC : Inv C) (huv : u ≠ v) {a b : St}
    (hδ : δ (C.st u) (C.st v) (C.edge u v) = (a, b, true)) (he : C.edge u v = false)
    (hdu : a.dg = (C.st u).dg + 1) (hdv : b.dg = (C.st v).dg + 1) (ha : ¬ a.Tok) (hb : b.Aw)
    (hbq : b ≠ q2') (hma : a = q2' → b.Mk) (hmb : b.Mk → a = q2')
    (hu0 : C.st u ≠ q2' ∧ ¬ (C.st u).Mk ∧ (C.deg u = 0 ∨ (C.st u).Tok))
    (hv0 : C.st v ≠ q2' ∧ ¬ (C.st v).Mk ∧ (C.deg v = 0 ∨ (C.st v).Tok))
    (hnr : ¬ C.active.Reachable u v)
    (hu : ∀ y, (C.st y).Tok → C.active.Reachable u y → y = u)
    (hv : ∀ y, (C.st y).Tok → C.active.Reachable v y → y = v) :
    Inv (P.interact C u v) := by
  have hδ' : P.δ (C.st u) (C.st v) (C.edge u v) = (a, b, true) := hδ
  obtain ⟨hDu, hDv, hDo⟩ := interact_states huv hδ
  have hG : (P.interact C u v).active = C.active ⊔ SimpleGraph.edge u v :=
    Protocol.interact_active_of_edge_true huv (by rw [hδ'])
  have hle : C.active ≤ (P.interact C u v).active := hG ▸ le_sup_left
  have hadj : (P.interact C u v).active.Adj u v := by
    rw [hG]; exact (SimpleGraph.sup_adj _ _ _ _).2 (.inr ((SimpleGraph.edge_adj _ _ _ _).2
      ⟨.inl ⟨rfl, rfl⟩, huv⟩))
  have hbT : b.Tok := St.tok_of_aw hb
  have hL : ∀ x, ((P.interact C u v).st x).Tok → x = v ∨ (x ≠ u ∧ x ≠ v ∧ (C.st x).Tok) := by
    intro x hx
    by_cases hxv : x = v
    · exact .inl hxv
    by_cases hxu : x = u
    · subst hxu; rw [hDu] at hx; exact absurd hx ha
    · exact .inr ⟨hxu, hxv, hDo x hxu hxv ▸ hx⟩
  -- old `q₂'` agents are not connected to `u` or `v`
  have hqu : ∀ x, C.st x = q2' → ¬ C.active.Reachable x u := fun x hx =>
    not_reach_q2' hC hx (hu0.2.2.imp_right fun h => ⟨h, hu0.2.1⟩)
  have hqv : ∀ x, C.st x = q2' → ¬ C.active.Reachable x v := fun x hx =>
    not_reach_q2' hC hx (hv0.2.2.imp_right fun h => ⟨h, hv0.2.1⟩)
  -- new `q₂'` agents: `u` (rules 3, 8) or old ones
  have hQ : ∀ x, (P.interact C u v).st x = q2' → (x = u ∧ a = q2') ∨
      (x ≠ u ∧ x ≠ v ∧ C.st x = q2') := by
    intro x hx
    by_cases hxu : x = u
    · subst hxu; rw [hDu] at hx; exact .inl ⟨rfl, hx⟩
    by_cases hxv : x = v
    · subst hxv; rw [hDv] at hx; exact absurd hx hbq
    · exact .inr ⟨hxu, hxv, hDo x hxu hxv ▸ hx⟩
  have hM : ∀ y, ((P.interact C u v).st y).Mk → y = v ∨ (y ≠ u ∧ y ≠ v ∧ (C.st y).Mk) := by
    intro y hy
    by_cases hyv : y = v
    · exact .inl hyv
    by_cases hyu : y = u
    · subst hyu; rw [hDu] at hy; exact absurd (St.tok_of_mk hy) ha
    · exact .inr ⟨hyu, hyv, hDo y hyu hyv ▸ hy⟩
  refine ⟨fun x => ?_, ?_, fun x hx => ?_, fun x y hx hy hxy => ?_, fun y hy => ?_,
    fun x hx => ?_, fun x y hx hy hxy => ?_, fun _ => ⟨v, hDv ▸ hb⟩⟩
  · -- degrees
    by_cases hxu : x = u
    · subst hxu
      rw [hDu, Protocol.deg_interact_activate_left huv he (by rw [hδ']), hdu, hC.dg]
    by_cases hxv : x = v
    · subst hxv
      rw [hDv, Protocol.deg_interact_activate_right huv he (by rw [hδ']), hdv, hC.dg]
    rw [hDo x hxu hxv, Protocol.deg_interact_other hxu hxv, hC.dg]
  · rw [hG]; exact (SimpleGraph.isAcyclic_add_edge_iff_of_not_reachable u v hnr).2 hC.acyclic
  · -- cover
    by_cases hxu : x = u
    · subst hxu; exact ⟨v, hDv ▸ hbT, hadj.reachable⟩
    by_cases hxv : x = v
    · subst hxv; exact ⟨x, hDv ▸ hbT, .rfl⟩
    rw [Protocol.deg_interact_other hxu hxv] at hx
    obtain ⟨y, hy, hxy⟩ := hC.cover x hx
    by_cases hyu : y = u
    · subst hyu; exact ⟨v, hDv ▸ hbT, (hxy.mono hle).trans hadj.reachable⟩
    by_cases hyv : y = v
    · subst hyv; exact ⟨y, hDv ▸ hbT, hxy.mono hle⟩
    · exact ⟨y, hDo y hyu hyv ▸ hy, hxy.mono hle⟩
  · -- uniqueness of tokens
    rw [hG, SimpleGraph.reachable_sup_edge_iff] at hxy
    have key : ∀ z, z = v ∨ (z ≠ u ∧ z ≠ v ∧ (C.st z).Tok) → ∀ t, (t = v ∨ (t ≠ u ∧ t ≠ v ∧
        (C.st t).Tok)) → C.active.Reachable z t → z = t := by
      rintro z (rfl | ⟨hzu, hzv, hz⟩) t (rfl | ⟨htu, htv, ht⟩) hzt
      · rfl
      · exact (hv t ht hzt).symm
      · exact hv z hz hzt.symm
      · exact hC.uniq z t hz ht hzt
    have hnu : ∀ z, z = v ∨ (z ≠ u ∧ z ≠ v ∧ (C.st z).Tok) → ¬ C.active.Reachable z u := by
      rintro z (rfl | ⟨hzu, -, hz⟩) hzu'
      · exact hnr hzu'.symm
      · exact hzu (hu z hz hzu'.symm)
    rcases hxy with h | ⟨h1, -⟩ | ⟨-, h2⟩
    · exact key x (hL x hx) y (hL y hy) h
    · exact absurd h1 (hnu x (hL x hx))
    · exact absurd h2.symm (hnu y (hL y hy))
  · -- mark1
    rcases hM y hy with rfl | ⟨hyu, hyv, hy'⟩
    · rw [hDv] at hy
      exact ⟨u, hadj.symm, hDu.trans (hmb hy)⟩
    · obtain ⟨x, hyx, hx⟩ := hC.mark1 y hy'
      have hxu : x ≠ u := fun h => hu0.1 (h ▸ hx)
      have hxv : x ≠ v := fun h => hv0.1 (h ▸ hx)
      exact ⟨x, hle hyx, (hDo x hxu hxv).trans hx⟩
  · -- mark2
    rcases hQ x hx with ⟨rfl, haq⟩ | ⟨hxu, hxv, hx'⟩
    · exact ⟨v, hadj, hDv ▸ hma haq⟩
    · obtain ⟨y, hxy, hy⟩ := hC.mark2 x hx'
      have hyu : y ≠ u := fun h => hu0.2.1 (h ▸ hy)
      have hyv : y ≠ v := fun h => hv0.2.1 (h ▸ hy)
      exact ⟨y, hle hxy, (hDo y hyu hyv).symm ▸ hy⟩
  · -- mark3
    rw [hG, SimpleGraph.reachable_sup_edge_iff] at hxy
    rcases hQ x hx with ⟨rfl, -⟩ | ⟨hxu, hxv, hx'⟩ <;>
      rcases hQ y hy with ⟨rfl, -⟩ | ⟨hyu, hyv, hy'⟩
    · rfl
    · exfalso
      rcases hxy with h | ⟨-, h⟩ | ⟨h, -⟩
      · exact hqu y hy' h.symm
      · exact hqv y hy' h.symm
      · exact hnr h
    · exfalso
      rcases hxy with h | ⟨h, -⟩ | ⟨h, -⟩
      · exact hqu x hx' h
      · exact hqu x hx' h
      · exact hqv x hx' h
    · rcases hxy with h | ⟨h, -⟩ | ⟨h, -⟩
      · exact hC.mark3 x y hx' hy' h
      · exact absurd h (hqu x hx')
      · exact absurd h (hqv x hx')

omit [Fintype V] [DecidableEq V] in
/-- In a forest, removing an edge disconnects its endpoints. -/
theorem not_reachable_sdiff_edge {G : SimpleGraph V} (hG : G.IsAcyclic) {x y : V} (h : G.Adj x y) :
    ¬ (G \ SimpleGraph.edge x y).Reachable x y := fun h' =>
  SimpleGraph.isBridge_iff.1 (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.1 hG h) h'

/-- Preservation of the invariant by rules 4 and 5: the `l'` token at `u` drops the edge to its
old neighbour `v`, which becomes the `f₁` token of the rest of its line (or an isolated `f₀`). -/
theorem inv_split (hC : Inv C) (huv : u ≠ v) {b : St}
    (hδ : δ (C.st u) (C.st v) (C.edge u v) = (l'', b, false)) (he : C.edge u v = true)
    (hu : C.st u = l') (hb : (b = f1 ∧ C.st v = q2) ∨ (b = f0 ∧ C.st v = q1)) :
    Inv (P.interact C u v) := by
  have hδ' : P.δ (C.st u) (C.st v) (C.edge u v) = (l'', b, false) := hδ
  obtain ⟨hDu, hDv, hDo⟩ := interact_states huv hδ
  have hG : (P.interact C u v).active = C.active \ SimpleGraph.edge u v :=
    Protocol.interact_active_of_edge_false (by rw [hδ'])
  have hle : (P.interact C u v).active ≤ C.active := hG ▸ sdiff_le
  have hadj : C.active.Adj u v := ⟨huv, he⟩
  have hkeep : ∀ a c, C.active.Adj a c → ¬ ((a = u ∧ c = v) ∨ (a = v ∧ c = u)) →
      (P.interact C u v).active.Adj a c := by
    intro a c h hne
    rw [hG, SimpleGraph.sdiff_adj, SimpleGraph.edge_adj]
    exact ⟨h, fun h' => hne h'.1⟩
  have hvT : ¬ (C.st v).Tok := by rcases hb with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> decide
  have hvq : C.st v ≠ q2' := by rcases hb with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> decide
  have hbq : b ≠ q2' := by rcases hb with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hbM : ¬ b.Mk := by rcases hb with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have huT : (C.st u).Tok := by rw [hu]; decide
  have hdv : (P.interact C u v).deg v + 1 = C.deg v :=
    Protocol.deg_interact_deactivate_right huv he (by rw [hδ'])
  have hdu : (P.interact C u v).deg u + 1 = C.deg u :=
    Protocol.deg_interact_deactivate_left huv he (by rw [hδ'])
  -- tokens after the step
  have hL : ∀ x, ((P.interact C u v).st x).Tok → x = v ∨ (x ≠ v ∧ (C.st x).Tok) := by
    intro x hx
    by_cases hxv : x = v
    · exact .inl hxv
    by_cases hxu : x = u
    · subst hxu; exact .inr ⟨hxv, huT⟩
    · exact .inr ⟨hxv, hDo x hxu hxv ▸ hx⟩
  have hsplit : ¬ (P.interact C u v).active.Reachable u v := by
    rw [hG]; exact not_reachable_sdiff_edge hC.acyclic hadj
  refine ⟨fun x => ?_, hC.acyclic.anti hle, fun x hx => ?_, fun x y hx hy hxy => ?_,
    fun y hy => ?_, fun x hx => ?_, fun x y hx hy hxy => ?_, fun _ => ⟨u, by rw [hDu]; decide⟩⟩
  · -- degrees
    by_cases hxu : x = u
    · subst hxu; rw [hDu]; have := hC.dg x; rw [hu] at this; simp [St.dg] at this ⊢; omega
    by_cases hxv : x = v
    · subst hxv; rw [hDv]; have := hC.dg x
      rcases hb with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> rw [h] at this <;> simp [St.dg] at this ⊢ <;> omega
    rw [hDo x hxu hxv, Protocol.deg_interact_other hxu hxv, hC.dg]
  · -- cover
    by_cases hxu : x = u
    · subst hxu; exact ⟨x, by rw [hDu]; decide, .rfl⟩
    by_cases hxv : x = v
    · subst hxv
      rcases hb with ⟨rfl, -⟩ | ⟨rfl, h⟩
      · exact ⟨x, by rw [hDv]; decide, .rfl⟩
      · exfalso; apply hx; have := hC.dg x; rw [h] at this; simp [St.dg] at this; omega
    rw [Protocol.deg_interact_other hxu hxv] at hx
    obtain ⟨y, hy, hxy⟩ := hC.cover x hx
    have hyv : y ≠ v := fun h => hvT (h ▸ hy)
    rcases (hG ▸ hxy.sdiff_edge (u := u) (v := v) :
      (P.interact C u v).active.Reachable x y ∨ (P.interact C u v).active.Reachable x u ∨
        (P.interact C u v).active.Reachable x v) with h | h | h
    · refine ⟨y, ?_, h⟩
      by_cases hyu : y = u
      · rw [hyu, hDu]; decide
      · rw [hDo y hyu hyv]; exact hy
    · exact ⟨u, by rw [hDu]; decide, h⟩
    · rcases hb with ⟨rfl, -⟩ | ⟨rfl, hq1⟩
      · exact ⟨v, by rw [hDv]; decide, h⟩
      · exfalso
        have h0 : (P.interact C u v).deg v = 0 := by
          have := hC.dg v; rw [hq1] at this; simp [St.dg] at this; omega
        exact hxv (eq_of_reachable_deg_zero h0 h)
  · -- uniqueness of tokens
    have hxy' := hxy.mono hle
    rcases hL x hx with rfl | ⟨hxv, hx'⟩ <;> rcases hL y hy with rfl | ⟨hyv, hy'⟩
    · rfl
    · exfalso
      have : y = u := (hC.uniq u y huT hy' (hadj.reachable.trans hxy')).symm
      subst this
      exact hsplit hxy.symm
    · exfalso
      have : x = u := hC.uniq x u hx' huT (hxy'.trans hadj.symm.reachable)
      subst this
      exact hsplit hxy
    · exact hC.uniq x y hx' hy' hxy'
  · -- mark1
    by_cases hyu : y = u
    · subst hyu
      obtain ⟨x, hyx, hx⟩ := hC.mark1 y (by rw [hu]; decide)
      have hxv : x ≠ v := fun h => hvq (h ▸ hx)
      have hxu : x ≠ y := fun h => by rw [h, hu] at hx; exact absurd hx (by decide)
      exact ⟨x, hkeep y x hyx (by tauto), (hDo x hxu hxv).trans hx⟩
    · have hyv : y ≠ v := fun h => hbM (by have := h ▸ hy; rwa [hDv] at this)
      rw [hDo y hyu hyv] at hy
      obtain ⟨x, hyx, hx⟩ := hC.mark1 y hy
      have hxv : x ≠ v := fun h => hvq (h ▸ hx)
      have hxu : x ≠ u := fun h => by rw [h, hu] at hx; exact absurd hx (by decide)
      exact ⟨x, hkeep y x hyx (by tauto), (hDo x hxu hxv).trans hx⟩
  · -- mark2
    have hxu : x ≠ u := fun h => by rw [h, hDu] at hx; exact absurd hx (by decide)
    have hxv : x ≠ v := fun h => hbq (by have := h ▸ hx; rwa [hDv] at this)
    rw [hDo x hxu hxv] at hx
    obtain ⟨y, hxy, hy⟩ := hC.mark2 x hx
    refine ⟨y, hkeep x y hxy (by tauto), ?_⟩
    by_cases hyu : y = u
    · rw [hyu, hDu]; decide
    have hyv : y ≠ v := fun h => hvT (h ▸ St.tok_of_mk hy)
    rw [hDo y hyu hyv]; exact hy
  · -- mark3
    have hq : ∀ z, (P.interact C u v).st z = q2' → C.st z = q2' := by
      intro z hz
      have hzu : z ≠ u := fun h => by rw [h, hDu] at hz; exact absurd hz (by decide)
      have hzv : z ≠ v := fun h => hbq (by have := h ▸ hz; rwa [hDv] at this)
      rwa [hDo z hzu hzv] at hz
    exact hC.mark3 x y (hq x hx) (hq y hy) (hxy.mono hle)

/-- Preservation of the invariant by rule 6: the `l''` token at `u` settles and the `q₂'` mark at
its neighbour `v` disappears. -/
theorem inv_settle (hC : Inv C) (huv : u ≠ v)
    (hδ : δ (C.st u) (C.st v) (C.edge u v) = (l, q2, true)) (he : C.edge u v = true)
    (hu : C.st u = l'') (hv : C.st v = q2') : Inv (P.interact C u v) := by
  have hδ' : P.δ (C.st u) (C.st v) (C.edge u v) = (l, q2, true) := hδ
  obtain ⟨hDu, hDv, hDo⟩ := interact_states huv hδ
  have hG : (P.interact C u v).active = C.active :=
    Protocol.interact_active_of_edge_eq (by rw [hδ', he])
  have hadj : C.active.Adj u v := ⟨huv, he⟩
  have huT : (C.st u).Tok := by rw [hu]; decide
  have hTok : ∀ x, ((P.interact C u v).st x).Tok ↔ (C.st x).Tok := by
    intro x
    by_cases hxu : x = u
    · subst hxu; rw [hDu, hu]; decide
    by_cases hxv : x = v
    · subst hxv; rw [hDv, hv]; decide
    rw [hDo x hxu hxv]
  refine ⟨fun x => ?_, hG ▸ hC.acyclic, fun x hx => ?_, fun x y hx hy hxy => ?_,
    fun y hy => ?_, fun x hx => ?_, fun x y hx hy hxy => ?_, fun _ => ⟨u, by rw [hDu]; decide⟩⟩
  · rw [Protocol.deg_interact_of_edge_eq (by rw [hδ', he])]
    by_cases hxu : x = u
    · subst hxu; rw [hDu, ← hC.dg, hu]; rfl
    by_cases hxv : x = v
    · subst hxv; rw [hDv, ← hC.dg, hv]; rfl
    rw [hDo x hxu hxv, hC.dg]
  · rw [Protocol.deg_interact_of_edge_eq (by rw [hδ', he])] at hx
    obtain ⟨y, hy, hxy⟩ := hC.cover x hx
    exact ⟨y, (hTok y).2 hy, hG ▸ hxy⟩
  · exact hC.uniq x y ((hTok x).1 hx) ((hTok y).1 hy) (hG ▸ hxy)
  · rw [hG]
    have hyu : y ≠ u := fun h => by rw [h, hDu] at hy; exact absurd hy (by decide)
    have hyv : y ≠ v := fun h => by rw [h, hDv] at hy; exact absurd hy (by decide)
    rw [hDo y hyu hyv] at hy
    obtain ⟨x, hyx, hx⟩ := hC.mark1 y hy
    have hxv : x ≠ v := by
      rintro rfl
      exact hyu (hC.uniq y u (St.tok_of_mk hy) huT (hyx.reachable.trans hadj.symm.reachable))
    have hxu : x ≠ u := fun h => by rw [h, hu] at hx; exact absurd hx (by decide)
    exact ⟨x, hyx, (hDo x hxu hxv).trans hx⟩
  · rw [hG]
    have hxu : x ≠ u := fun h => by rw [h, hDu] at hx; exact absurd hx (by decide)
    have hxv : x ≠ v := fun h => by rw [h, hDv] at hx; exact absurd hx (by decide)
    rw [hDo x hxu hxv] at hx
    obtain ⟨y, hxy, hy⟩ := hC.mark2 x hx
    have hyu : y ≠ u := by
      rintro rfl
      exact hxv (hC.mark3 x v hx hv (hxy.reachable.trans hadj.reachable))
    have hyv : y ≠ v := fun h => by rw [h, hv] at hy; exact absurd hy (by decide)
    exact ⟨y, hxy, (hDo y hyu hyv).symm ▸ hy⟩
  · have hq : ∀ z, (P.interact C u v).st z = q2' → C.st z = q2' := by
      intro z hz
      have hzu : z ≠ u := fun h => by rw [h, hDu] at hz; exact absurd hz (by decide)
      have hzv : z ≠ v := fun h => by rw [h, hDv] at hz; exact absurd hz (by decide)
      rwa [hDo z hzu hzv] at hz
    exact hC.mark3 x y (hq x hx) (hq y hy) (hG ▸ hxy)

theorem inv_step {C D : Config V St} (hC : Inv C) (h : P.Step C D) : Inv D := by
  obtain ⟨u, v, huv, rfl⟩ := h
  have iso : ∀ x, (C.st x).dg = 0 → C.deg x = 0 := fun x hx => by rw [← hC.dg, hx]
  have tokl : ∀ x, C.st x = l → C.st x ≠ q2' ∧ ¬ (C.st x).Mk ∧ (C.deg x = 0 ∨ (C.st x).Tok) :=
    fun x hx => by rw [hx]; exact ⟨by decide, by decide, .inr (by decide)⟩
  have isol : ∀ x, (C.st x).dg = 0 → C.st x ≠ q2' → ¬ (C.st x).Mk →
      C.st x ≠ q2' ∧ ¬ (C.st x).Mk ∧ (C.deg x = 0 ∨ (C.st x).Tok) :=
    fun x hx h1 h2 => ⟨h1, h2, .inl (iso x hx)⟩
  have isoR : ∀ x y, (C.st x).dg = 0 → C.active.Reachable x y → y = x :=
    fun x y hx h => eq_of_reachable_deg_zero (iso x hx) h.symm
  have tokR : ∀ x y, (C.st x).Tok → (C.st y).Tok → C.active.Reachable x y → y = x :=
    fun x y hx hy h => (hC.uniq x y hx hy h).symm
  rcases δ_cases (C.st u) (C.st v) (C.edge u v) with h | ⟨hu, hv, he, h⟩ | ⟨hu, hv, he, h⟩ |
    ⟨hu, hv, he, h⟩ | ⟨hu, hv, he, h⟩ | ⟨hu, hv, he, h⟩ | ⟨hu, hv, he, h⟩ | ⟨hu, hv, he, h⟩ |
    ⟨hu, hv, he, h⟩
  · rw [Protocol.interact_eq_self C h]; exact hC
  · -- rule 1
    have hu0 : (C.st u).dg = 0 := by rw [hu]; rfl
    have hv0 : (C.st v).dg = 0 := by rw [hv]; rfl
    exact inv_activate hC huv h he (by rw [hu]; rfl) (by rw [hv]; rfl) (by decide) (by decide)
      (by decide) (by decide) (by decide) (isol u hu0 (by rw [hu]; decide) (by rw [hu]; decide))
      (isol v hv0 (by rw [hv]; decide) (by rw [hv]; decide))
      (fun h => huv (isoR v u hv0 h.symm)) (fun y _ h => isoR u y hu0 h)
      (fun y _ h => isoR v y hv0 h)
  · -- rule 2
    have hv0 : (C.st v).dg = 0 := by rw [hv]; rfl
    exact inv_activate hC huv h he (by rw [hu]; rfl) (by rw [hv]; rfl) (by decide) (by decide)
      (by decide) (by decide) (by decide) (tokl u hu)
      (isol v hv0 (by rw [hv]; decide) (by rw [hv]; decide))
      (fun h => huv (isoR v u hv0 h.symm)) (fun y hy h => tokR u y (by rw [hu]; decide) hy h)
      (fun y _ h => isoR v y hv0 h)
  · -- rule 3
    have huT : (C.st u).Tok := by rw [hu]; decide
    have hvT : (C.st v).Tok := by rw [hv]; decide
    exact inv_activate hC huv h he (by rw [hu]; rfl) (by rw [hv]; rfl) (by decide) (by decide)
      (by decide) (by decide) (by decide) (tokl u hu) (tokl v hv)
      (fun h => huv (hC.uniq u v huT hvT h)) (fun y hy h => tokR u y huT hy h)
      (fun y hy h => tokR v y hvT hy h)
  · exact inv_split hC huv h he hu (.inl ⟨rfl, hv⟩)
  · exact inv_split hC huv h he hu (.inr ⟨rfl, hv⟩)
  · exact inv_settle hC huv h he hu hv
  · -- rule 7
    have hv0 : (C.st v).dg = 0 := by rw [hv]; rfl
    exact inv_activate hC huv h he (by rw [hu]; rfl) (by rw [hv]; rfl) (by decide) (by decide)
      (by decide) (by decide) (by decide) (tokl u hu)
      (isol v hv0 (by rw [hv]; decide) (by rw [hv]; decide))
      (fun h => huv (isoR v u hv0 h.symm)) (fun y hy h => tokR u y (by rw [hu]; decide) hy h)
      (fun y _ h => isoR v y hv0 h)
  · -- rule 8
    have huT : (C.st u).Tok := by rw [hu]; decide
    have hvT : (C.st v).Tok := by rw [hv]; decide
    exact inv_activate hC huv h he (by rw [hu]; rfl) (by rw [hv]; rfl) (by decide) (by decide)
      (by decide) (by decide) (by decide) (tokl u hu)
      (by rw [hv]; exact ⟨by decide, by decide, .inr (by decide)⟩)
      (fun h => huv (hC.uniq u v huT hvT h)) (fun y hy h => tokR u y huT hy h)
      (fun y hy h => tokR v y hvT hy h)

theorem inv_reach {C D : Config V St} (hC : Inv C) (h : P.Reachable C D) : Inv D := by
  induction h with
  | refl => exact hC
  | tail _ hst ih => exact inv_step ih hst

end step

end Podc.NetworkConstructors.FastLine
