import Papers.PODC2014.NetworkConstructors.Problems

/-!
# Protocol 5 (Global-Star) constructs a spanning star (Theorem 8, correctness)

Two states, `c` (center, initial) and `p` (peripheral):
`(c, c, 0) → (c, p, 1)`, `(p, p, 1) → (p, p, 0)`, `(c, p, 0) → (c, p, 1)`.

Invariant: there is a center, and no active edge joins two centers. Centers only disappear (two
centers meet), so eventually one center `c₀` remains; then `c`–`p` edges get activated and `p`–`p`
edges deactivated. The final configurations (one center, active edges = edges at the center) are
silent.
-/

namespace Podc.NetworkConstructors.Star

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem

/-- States of Protocol 5 (Global-Star). -/
inductive St | c | p
  deriving DecidableEq, Repr

open St

instance : Fintype St := ⟨{c, p}, fun x => by cases x <;> simp⟩

/-- The transition function of Protocol 5; unlisted triples are ineffective. -/
def δ : St → St → Bool → St × St × Bool
  | c, c, false => (c, p, true)
  | p, p, true => (p, p, false)
  | c, p, false => (c, p, true)
  | a, b, e => (a, b, e)

/-- Protocol 5 (Global-Star): initial state `c`, all states are output states. -/
def P : Protocol St where
  init := c
  out _ := true
  δ := δ

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The inductive invariant: some center exists, and no active edge joins two centers. -/
def Inv (C : Config V St) : Prop :=
  (∃ u, C.st u = c) ∧ ∀ u v, C.st u = c → C.st v = c → C.edge u v = false

/-- The final configurations: a unique center `c₀`, and an edge is active iff it is incident to
`c₀`. -/
def Final (C : Config V St) : Prop :=
  ∃ c₀, (∀ u, C.st u = c ↔ u = c₀) ∧ ∀ u v, u ≠ v → (C.edge u v = true ↔ (u = c₀ ∨ v = c₀))

omit [Fintype V] in
theorem interact_st (C : Config V St) (u v x : V) :
    (P.interact C u v).st x = if x = u then (δ (C.st u) (C.st v) (C.edge u v)).1
      else if x = v then (δ (C.st u) (C.st v) (C.edge u v)).2.1 else C.st x := rfl

omit [Fintype V] in
theorem interact_edge (C : Config V St) (u v x y : V) :
    (P.interact C u v).edge x y = if (x = u ∧ y = v) ∨ (x = v ∧ y = u) then
      (δ (C.st u) (C.st v) (C.edge u v)).2.2 else C.edge x y := rfl

omit [Fintype V] in
/-- Centers never appear: a center after a step was a center before. -/
theorem st_c_of_interact {C : Config V St} {u v x : V} (h : (P.interact C u v).st x = c) :
    C.st x = c := by
  rw [interact_st] at h
  split_ifs at h with h1 h2
  · subst h1
    revert h; cases C.st x <;> cases C.st v <;> cases C.edge x v <;> simp [δ]
  · subst h2
    revert h; cases C.st u <;> cases C.st x <;> cases C.edge u x <;> simp [δ]
  · exact h

omit [Fintype V] [DecidableEq V] in
theorem inv_init [Nonempty V] : Inv (P.initConfig : Config V St) :=
  ⟨⟨Classical.arbitrary V, rfl⟩, fun _ _ _ _ => rfl⟩

omit [Fintype V] in
theorem inv_step {C D : Config V St} (hC : Inv C) (h : P.Step C D) : Inv D := by
  obtain ⟨u, v, huv, rfl⟩ := h
  obtain ⟨⟨w, hw⟩, he⟩ := hC
  refine ⟨?_, fun x y hx hy => ?_⟩
  · -- the initiator of a step that kills a center stays a center
    by_cases hwv : w = v
    · subst hwv
      by_cases hu : C.st u = c
      · exact ⟨u, by rw [interact_st]; simp only; rw [hu, hw]; cases C.edge u w <;> rfl⟩
      · refine ⟨w, ?_⟩
        rw [interact_st, ite_eq_right huv.symm, ite_eq_left rfl, hw]
        cases h : C.st u
        · exact absurd h hu
        · cases C.edge u w <;> rfl
    · by_cases hwu : w = u
      · subst hwu
        refine ⟨w, ?_⟩
        rw [interact_st, ite_eq_left rfl, hw]
        cases C.st v <;> cases C.edge w v <;> rfl
      · exact ⟨w, by rw [interact_st, ite_eq_right hwu, ite_eq_right hwv, hw]⟩
  · have hx' := st_c_of_interact hx
    have hy' := st_c_of_interact hy
    rw [interact_edge]
    split_ifs with hxy
    · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hx', hy', he _ _ hx' hy']
        -- both stay centers only if the rule is not `(c, c, 0)`, which makes `y` peripheral
        exfalso
        rw [interact_st, ite_eq_right huv.symm, ite_eq_left rfl, hx', hy', he _ _ hx' hy'] at hy
        simp [δ] at hy
      · rw [hx', hy', he _ _ hy' hx']
        exfalso
        rw [interact_st, ite_eq_right huv.symm, ite_eq_left rfl, hx', hy', he _ _ hy' hx'] at hx
        simp [δ] at hx
    · exact he _ _ hx' hy'

omit [Fintype V] in
theorem inv_reachable [Nonempty V] {C : Config V St} (h : P.Reachable P.initConfig C) : Inv C := by
  induction h with
  | refl => exact inv_init
  | tail _ hst ih => exact inv_step ih hst

omit [Fintype V] in
/-- Final configurations are silent. -/
theorem final_silent {C : Config V St} (hC : Final C) {u v : V} (huv : u ≠ v) :
    P.interact C u v = C := by
  obtain ⟨c₀, hc, he⟩ := hC
  apply Protocol.interact_eq_self
  have heuv := he u v huv
  have hu := hc u
  have hv := hc v
  show δ _ _ _ = _
  cases hsu : C.st u <;> cases hsv : C.st v <;> cases hce : C.edge u v <;>
    simp_all [δ]

omit [Fintype V] in
theorem final_step {C D : Config V St} (hC : Final C) (h : P.Step C D) : D = C := by
  obtain ⟨u, v, huv, rfl⟩ := h
  exact final_silent hC huv

theorem final_spanningStar {C : Config V St} (hC : Final C) : IsSpanningStar (P.output C) := by
  have hout : ∀ q, P.out q = true := fun _ => rfl
  obtain ⟨c₀, hc, he⟩ := hC
  refine ⟨Protocol.output_verts_univ hout C, ?_, c₀, ?_, fun v hv => ?_⟩
  · rw [Protocol.output_connected_iff hout]
    have hadj : ∀ v, v ≠ c₀ → C.active.Adj c₀ v := fun v hv =>
      ⟨Ne.symm hv, (he c₀ v (Ne.symm hv)).2 (.inl rfl)⟩
    refine SimpleGraph.connected_iff_exists_forall_reachable _ |>.2 ⟨c₀, fun v => ?_⟩
    by_cases hv : v = c₀
    · subst hv; rfl
    · exact (hadj v hv).reachable
  · rw [Protocol.ncard_neighborSet_output hout, Config.deg]
    rw [show (Finset.univ.filter fun v => v ≠ c₀ ∧ C.edge c₀ v = true) = Finset.univ.erase c₀ by
      ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · exact fun h => ⟨h.1, trivial⟩
      · exact fun h => ⟨h.1, (he c₀ v (Ne.symm h.1)).2 (.inl rfl)⟩]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  · rw [Protocol.ncard_neighborSet_output hout, Config.deg, Finset.card_eq_one]
    refine ⟨c₀, ?_⟩
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨hwv, hw⟩
      rcases (he v w (Ne.symm hwv)).1 hw with h | h
      · exact absurd h hv
      · exact h
    · intro hw
      rw [hw]
      exact ⟨Ne.symm hv, (he v c₀ hv).2 (.inr rfl)⟩

/-- The number of centers. -/
def ncenters (C : Config V St) : ℕ := (Finset.univ.filter fun u => C.st u = c).card

/-- A pair whose edge state is wrong for a star around the (unique) center: the edge should be
active iff exactly one endpoint is a center. -/
def bad (C : Config V St) : Finset (V × V) :=
  Finset.univ.filter fun e => e.1 ≠ e.2 ∧ (C.edge e.1 e.2 = true ↔ (C.st e.1 = c ↔ C.st e.2 = c))

/-- Phase 1: two centers meet until one is left. -/
theorem reach_one_center {C : Config V St} (hC : Inv C) :
    ∃ D, P.Reachable C D ∧ Inv D ∧ ncenters D = 1 := by
  refine exists_reach_of_measure (R := P.Step) Inv (fun D => ncenters D = 1) ncenters ?_ C hC
  intro D hD hne
  obtain ⟨⟨w, hw⟩, he⟩ := hD
  have hpos : 0 < ncenters D := Finset.card_pos.2 ⟨w, by simp [hw]⟩
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (show 1 < ncenters D by omega)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
  refine ⟨P.interact D u v, Protocol.reachable_of_ne huv, inv_step ⟨⟨w, hw⟩, he⟩
    (Protocol.step_of_ne huv), ?_⟩
  apply Finset.card_lt_card
  refine ⟨fun x hx => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact st_c_of_interact hx
  · have : v ∈ Finset.univ.filter fun x => (P.interact D u v).st x = c :=
      hsub (by simp [hv])
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    rw [interact_st, ite_eq_right (Ne.symm huv), ite_eq_left rfl, hu, hv, he u v hu hv] at this
    simp [δ] at this

theorem final_of_inv {C : Config V St} (_hC : Inv C) (h1 : ncenters C = 1)
    (hb : bad C = ∅) : Final C := by
  obtain ⟨c₀, hc₀⟩ := Finset.card_eq_one.1 h1
  have hc : ∀ u, C.st u = c ↔ u = c₀ := fun u => by
    have := congrArg (u ∈ ·) hc₀
    simpa using this
  refine ⟨c₀, hc, fun u v huv => ?_⟩
  have hnb : (u, v) ∉ bad C := by simp [hb]
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_and] at hnb
  have := hnb huv
  rw [hc, hc] at this
  by_cases hu : u = c₀ <;> by_cases hv : v = c₀
  · exact absurd (hu.trans hv.symm) huv
  · simp_all
  · simp_all
  · simp_all

/-- Phase 2: with a unique center, fix the wrong edges one at a time. -/
theorem reach_final {C : Config V St} (hC : Inv C) (h1 : ncenters C = 1) :
    ∃ D, P.Reachable C D ∧ Final D := by
  suffices h : ∀ D : Config V St, Inv D ∧ ncenters D = 1 → ¬ bad D = ∅ → ∃ E, P.Reachable D E ∧
      (Inv E ∧ ncenters E = 1) ∧ (bad E).card < (bad D).card by
    obtain ⟨D, hCD, ⟨hD, hD1⟩, hb⟩ := exists_reach_of_measure (R := P.Step)
      (fun D => Inv D ∧ ncenters D = 1) (fun D => bad D = ∅) (fun D => (bad D).card) h C ⟨hC, h1⟩
    exact ⟨D, hCD, final_of_inv hD hD1 hb⟩
  intro D ⟨hD, hD1⟩ hne
  obtain ⟨⟨a, b⟩, hab⟩ := Finset.nonempty_iff_ne_empty.2 hne
  obtain ⟨c₀, hc₀⟩ := Finset.card_eq_one.1 hD1
  have hc : ∀ u, D.st u = c ↔ u = c₀ := fun u => by
    have := congrArg (u ∈ ·) hc₀
    simpa using this
  simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and] at hab
  obtain ⟨hab, hwrong⟩ := hab
  -- orient the interaction: the center (if any) initiates
  obtain ⟨u, v, huv, hpair, hstep⟩ : ∃ u v, u ≠ v ∧ ((u = a ∧ v = b) ∨ (u = b ∧ v = a)) ∧
      (P.interact D u v).st = D.st ∧ (P.interact D u v).edge u v = !D.edge u v := by
    have key : ∀ u v, u ≠ v → (D.edge u v = true ↔ (D.st u = c ↔ D.st v = c)) →
        D.st v = p → (P.interact D u v).st = D.st ∧ (P.interact D u v).edge u v = !D.edge u v := by
      intro u v huv hw hv
      have hst : (δ (D.st u) (D.st v) (D.edge u v)).1 = D.st u ∧
          (δ (D.st u) (D.st v) (D.edge u v)).2.1 = D.st v ∧
          (δ (D.st u) (D.st v) (D.edge u v)).2.2 = !D.edge u v := by
        rw [hv] at hw ⊢
        cases hsu : D.st u <;> cases hce : D.edge u v <;> simp_all [δ]
      refine ⟨funext fun x => ?_, ?_⟩
      · rw [interact_st]
        split_ifs with h1 h2
        · subst h1; exact hst.1
        · subst h2; exact hst.2.1
        · rfl
      · rw [interact_edge, ite_eq_left (.inl ⟨rfl, rfl⟩)]
        exact hst.2.2
    by_cases hb : D.st b = c
    · have ha : D.st a = p := by
        cases h : D.st a
        · exact absurd (((hc a).1 h).trans ((hc b).1 hb).symm) hab
        · rfl
      exact ⟨b, a, Ne.symm hab, .inr ⟨rfl, rfl⟩,
        key b a (Ne.symm hab) (by rw [D.symm]; tauto) ha⟩
    · have hb' : D.st b = p := by cases h : D.st b <;> simp_all
      exact ⟨a, b, hab, .inl ⟨rfl, rfl⟩, key a b hab hwrong hb'⟩
  have hnew : ∀ x y, (P.interact D u v).edge x y =
      if (x = a ∧ y = b) ∨ (x = b ∧ y = a) then !D.edge x y else D.edge x y := by
    intro x y
    have hxy : ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) ↔ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) := by
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto
    rw [interact_edge]
    by_cases h : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
    · rw [ite_eq_left h, ite_eq_left (hxy.1 h)]
      have := hstep.2
      rw [interact_edge, ite_eq_left (.inl ⟨rfl, rfl⟩)] at this
      rw [this]
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · rw [D.symm]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (hxy.2 h'))]
  have hwrong' : D.edge b a = true ↔ (D.st b = c ↔ D.st a = c) := by
    rw [D.symm]; tauto
  refine ⟨P.interact D u v, Protocol.reachable_of_ne huv,
    ⟨inv_step hD (Protocol.step_of_ne huv), ?_⟩, ?_⟩
  · simp only [ncenters, hstep.1]; exact hD1
  · apply Finset.card_lt_card
    refine ⟨fun e he => ?_, fun hsub => ?_⟩
    · simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, hstep.1, hnew] at he ⊢
      refine ⟨he.1, ?_⟩
      have := he.2
      split_ifs at this with h
      · exfalso
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2] at this
          cases hd : D.edge a b <;> simp_all
        · rw [h1, h2] at this
          cases hd : D.edge b a <;> simp_all
      · exact this
    · have hmem : (a, b) ∈ bad D := by
        simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hab, hwrong⟩
      have := hsub hmem
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, hstep.1, hnew, and_self,
        true_or, ite_true] at this
      cases hd : D.edge a b <;> simp_all

/-- **Theorem 8 (correctness) of Michail–Spirakis.** Protocol Global-Star constructs a spanning
star, on any number `n ≥ 1` of agents and under every globally fair scheduler. -/
theorem constructs_spanningStar [Nonempty V] : P.Constructs (V := V) IsSpanningStar := by
  refine P.constructs_of_reach {C | Final C} (fun C D hC hCD => ?_) (fun C D hC hCD => ?_)
    (fun C hC => final_spanningStar hC) (fun C hC => ?_)
  · rw [Set.mem_ofPred_eq, final_step hC hCD]; exact hC
  · rw [final_step hC hCD]
  · obtain ⟨D, hCD, hD, hD1⟩ := reach_one_center (inv_reachable hC)
    obtain ⟨E, hDE, hE⟩ := reach_final hD hD1
    exact ⟨E, hE, hCD.trans hDE⟩

/-! ### Theorem 7, first part: one state does not suffice -/

section oneState

variable (Q : Protocol Unit)

/-- The edge rule of a one-state protocol. -/
def f1 (c : Bool) : Bool := (Q.δ () () c).2.2

theorem δ_unit (c : Bool) : Q.δ () () c = ((), (), f1 Q c) := rfl

theorem interact_edge_eq (C : Config (Fin 3) Unit) (u v : Fin 3) :
    (Q.interact C u v).edge u v = f1 Q (C.edge u v) := by
  rw [Protocol.interact_edge_uv]; rfl

theorem interact_edge_of (C : Config (Fin 3) Unit) {u v x y : Fin 3}
    (h : (x = u ∧ y = v) ∨ (x = v ∧ y = u)) : (Q.interact C u v).edge x y = f1 Q (C.edge u v) := by
  simp only [Protocol.interact, h, ite_true]; rfl

/-- **Theorem 7, first part (state lower bound), of Michail–Spirakis.** No protocol with a single
state constructs a spanning star (already on `n = 3` agents): either no edge is ever activated,
or all edges end up active (a triangle), or edges toggle forever. -/
theorem star_needs_two_states : ¬ Q.Constructs (V := Fin 3) IsSpanningStar := by
  intro hc
  obtain ⟨E, hE0, hfair⟩ := Q.exists_fair_execution (V := Fin 3)
  obtain ⟨H, hH, hev⟩ := hc E hE0 hfair
  have hout : Q.out () = true := by
    by_contra h
    obtain ⟨t, ht⟩ := hev.exists
    have h0 : (0 : Fin 3) ∈ (Q.output (E.st t)).verts := by rw [ht, hH.1]; trivial
    simp [Protocol.output, h] at h0
  have hadj : ∀ (C : Config (Fin 3) Unit) u v, (Q.output C).Adj u v ↔ u ≠ v ∧ C.edge u v = true :=
    by simp [Protocol.output, hout]
  have hns : ∀ (C : Config (Fin 3) Unit) v,
      (Q.output C).neighborSet v = {w | v ≠ w ∧ C.edge v w = true} := by
    intro C v; ext w; exact hadj C v w
  cases hf0 : f1 Q false
  · -- no edge is ever activated
    have hall : ∀ t, E.st t = Q.initConfig := by
      intro t
      induction t with
      | zero => exact hE0
      | succ t ih =>
        obtain ⟨u, v, -, h⟩ := E.step t
        rw [h, ih]
        apply Protocol.interact_eq_self
        rw [δ_unit]; simp only [Protocol.initConfig] at hf0 ⊢; rw [hf0]
    obtain ⟨t, ht⟩ := hev.exists
    obtain ⟨c, hc', -⟩ := hH.2.2
    rw [← ht, hall t, hns] at hc'
    simp [Protocol.initConfig] at hc'
  cases hf1 : f1 Q true
  · -- edges toggle forever
    refine Q.not_constructs_of_unstable (C := Q.initConfig) .refl (fun D _ => ?_) hc
    refine ⟨D, Q.interact D 0 1, .refl, Protocol.reachable_of_ne (by decide), fun h => ?_⟩
    have := congrArg (fun H : (⊤ : SimpleGraph (Fin 3)).Subgraph => H.Adj 0 1) h
    simp only [hadj, interact_edge_of Q D (Or.inl ⟨rfl, rfl⟩)] at this
    cases hd : D.edge 0 1 <;> simp_all
  · -- all edges end up active: a triangle
    set S : Set (Config (Fin 3) Unit) := {C | ∀ u v, u ≠ v → C.edge u v = true}
    have hkeep : ∀ (C : Config (Fin 3) Unit) u v x y, C.edge x y = true →
        (Q.interact C u v).edge x y = true := by
      intro C u v x y h
      by_cases hxy : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
      · rw [interact_edge_of Q C hxy]
        rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rw [h]; exact hf1
        · rw [C.symm] at h; rw [h]; exact hf1
      · rw [Protocol.interact_edge_other C hxy]; exact h
    have hset : ∀ (C : Config (Fin 3) Unit) u v, (Q.interact C u v).edge u v = true := by
      intro C u v
      rw [interact_edge_of Q C (Or.inl ⟨rfl, rfl⟩)]
      cases C.edge u v
      · exact hf0
      · exact hf1
    have hS : IsTrap Q.Step S := by
      rintro C D hC ⟨u, v, -, rfl⟩ x y hxy
      exact hkeep C u v x y (hC x y hxy)
    have hreach : ∀ C, Q.Reachable (E.st 0) C → ∃ D ∈ S, Q.Reachable C D := by
      intro C _
      refine ⟨Q.interact (Q.interact (Q.interact C 0 1) 0 2) 1 2, ?_,
        ((Protocol.reachable_of_ne (by decide)).trans (Protocol.reachable_of_ne (by decide))).trans
          (Protocol.reachable_of_ne (by decide))⟩
      have h01 := hkeep _ 1 2 0 1 (hkeep _ 0 2 0 1 (hset C 0 1))
      have h02 := hkeep _ 1 2 0 2 (hset (Q.interact C 0 1) 0 2)
      have h12 := hset (Q.interact (Q.interact C 0 1) 0 2) 1 2
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all
    obtain ⟨t, htS, ht⟩ := ((hfair.eventually_mem hS hreach).and hev).exists
    obtain ⟨c, -, hc'⟩ := hH.2.2
    obtain ⟨v, hv⟩ : ∃ v : Fin 3, v ≠ c := ⟨c + 1, by fin_cases c <;> decide⟩
    have := hc' v hv
    rw [← ht, hns] at this
    have hset' : {w | v ≠ w ∧ (E.st t).edge v w = true} = ({w | w ≠ v} : Set (Fin 3)) := by
      ext w; simp only [Set.mem_ofPred_eq]
      exact ⟨fun h => Ne.symm h.1, fun h => ⟨Ne.symm h, htS v w (Ne.symm h)⟩⟩
    rw [hset', show ({w | w ≠ v} : Set (Fin 3)) = ↑(Finset.univ.erase v) by ext; simp,
      Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_univ _)] at this
    simp at this

end oneState

end Podc.NetworkConstructors.Star
