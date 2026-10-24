import Papers.PODC2014.NetworkConstructors.Problems

/-!
# Protocol 1 (Simple-Global-Line) constructs a spanning line (Theorem 3, correctness)

States `q₀, q₁, q₂, l, w`; rules
`(q₀, q₀, 0) → (q₁, l, 1)`, `(l, q₀, 0) → (q₂, l, 1)`, `(l, l, 0) → (q₂, w, 1)`,
`(w, q₂, 1) → (q₂, w, 1)`, `(w, q₁, 1) → (q₂, l, 1)`.

Invariant (`Inv`), as in the paper: the active graph is a forest of paths (acyclic, the degree of
an agent is determined by its state: `q₀ ↦ 0`, `q₁, l ↦ 1`, `q₂, w ↦ 2`), and every non-trivial
component contains exactly one *leader* (`l` or `w`). The final configurations (no `q₀`, a unique
leader) have a spanning line as active graph and only the leader moves (`final_step_edge`). From
every reachable configuration a final one is reachable: move a `w` leader along its line to an
endpoint (`move_w`), let a leader absorb an isolated agent, or merge two lines.
-/

namespace Podc.NetworkConstructors.SimpleLine

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem

/-- States of Protocol 1 (Simple-Global-Line). -/
inductive St | q0 | q1 | q2 | l | w
  deriving DecidableEq, Repr

open St

instance : Fintype St := ⟨{q0, q1, q2, l, w}, fun x => by cases x <;> simp⟩

/-- The degree of an agent in a given state. -/
def St.dg : St → ℕ
  | q0 => 0
  | q1 => 1
  | l => 1
  | q2 => 2
  | w => 2

/-- Leader states. -/
def St.IsL (s : St) : Prop := s = l ∨ s = w

instance : DecidablePred St.IsL := fun s => by unfold St.IsL; infer_instance

/-- The transition function of Protocol 1; unlisted triples are ineffective. -/
def δ : St → St → Bool → St × St × Bool
  | q0, q0, false => (q1, l, true)
  | l, q0, false => (q2, l, true)
  | l, l, false => (q2, w, true)
  | w, q2, true => (q2, w, true)
  | w, q1, true => (q2, l, true)
  | a, b, e => (a, b, e)

/-- Protocol 1 (Simple-Global-Line): initial state `q₀`, all states are output states. -/
def P : Protocol St where
  init := q0
  out _ := true
  δ := δ

/-- The effective rules, as a disjunction. -/
theorem δ_cases (a b : St) (e : Bool) :
    δ a b e = (a, b, e) ∨
    (a = q0 ∧ b = q0 ∧ e = false ∧ δ a b e = (q1, l, true)) ∨
    (a = l ∧ b = q0 ∧ e = false ∧ δ a b e = (q2, l, true)) ∨
    (a = l ∧ b = l ∧ e = false ∧ δ a b e = (q2, w, true)) ∨
    (a = w ∧ b = q2 ∧ e = true ∧ δ a b e = (q2, w, true)) ∨
    (a = w ∧ b = q1 ∧ e = true ∧ δ a b e = (q2, l, true)) := by
  cases a <;> cases b <;> cases e <;> simp [δ]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The inductive invariant. -/
structure Inv (C : Config V St) : Prop where
  dg : ∀ u, (C.st u).dg = C.deg u
  acyclic : C.active.IsAcyclic
  cover : ∀ u, C.st u ≠ q0 → ∃ x, (C.st x).IsL ∧ C.active.Reachable u x
  uniq : ∀ x y, (C.st x).IsL → (C.st y).IsL → C.active.Reachable x y → x = y

theorem st_eq_q0_iff {C : Config V St} (hC : Inv C) {u : V} : C.st u = q0 ↔ C.deg u = 0 := by
  rw [← hC.dg]; cases C.st u <;> simp [St.dg]

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

theorem inv_init : Inv (P.initConfig : Config V St) where
  dg u := by simp [Protocol.initConfig, Config.deg, St.dg, P]
  acyclic := by
    have : (P.initConfig : Config V St).active = ⊥ := by
      ext u v; simp [Protocol.initConfig, Config.active_adj]
    rw [this]; exact SimpleGraph.isAcyclic_bot
  cover u h := absurd rfl h
  uniq x _ hx := by simp [Protocol.initConfig, P, St.IsL] at hx

section step

variable {C : Config V St} {u v : V}

omit [Fintype V] in
theorem interact_st_eq (C : Config V St) (u v x : V) :
    (P.interact C u v).st x = if x = u then (δ (C.st u) (C.st v) (C.edge u v)).1
      else if x = v then (δ (C.st u) (C.st v) (C.edge u v)).2.1 else C.st x := rfl

/-- Preservation of the invariant by an activation that joins two different components; `u`
stops being a leader, `v` becomes (or stays) one. -/
theorem inv_activate (hC : Inv C) (huv : u ≠ v) {a b : St}
    (hδ : δ (C.st u) (C.st v) (C.edge u v) = (a, b, true)) (he : C.edge u v = false)
    (hdu : a.dg = (C.st u).dg + 1) (hdv : b.dg = (C.st v).dg + 1) (ha : ¬ a.IsL) (hb : b.IsL)
    (hnr : ¬ C.active.Reachable u v)
    (hu : ∀ y, (C.st y).IsL → C.active.Reachable u y → y = u)
    (hv : ∀ y, (C.st y).IsL → C.active.Reachable v y → y = v) :
    Inv (P.interact C u v) := by
  have hδ' : P.δ (C.st u) (C.st v) (C.edge u v) = (a, b, true) := hδ
  have hDu : (P.interact C u v).st u = a := by rw [interact_st_eq, ite_eq_left rfl, hδ]
  have hDv : (P.interact C u v).st v = b := by
    rw [interact_st_eq, ite_eq_right (Ne.symm huv), ite_eq_left rfl, hδ]
  have hDo : ∀ x, x ≠ u → x ≠ v → (P.interact C u v).st x = C.st x :=
    fun x hxu hxv => Protocol.interact_st_other C hxu hxv
  have hG : (P.interact C u v).active = C.active ⊔ SimpleGraph.edge u v :=
    Protocol.interact_active_of_edge_true huv (by rw [hδ'])
  have hle : C.active ≤ (P.interact C u v).active := hG ▸ le_sup_left
  have hadj : (P.interact C u v).active.Adj u v := by
    rw [hG]; exact (SimpleGraph.sup_adj _ _ _ _).2 (.inr ((SimpleGraph.edge_adj _ _ _ _).2
      ⟨.inl ⟨rfl, rfl⟩, huv⟩))
  -- a leader of the new configuration is `v` or an old leader different from `u`
  have hL : ∀ x, ((P.interact C u v).st x).IsL → x = v ∨ (x ≠ u ∧ x ≠ v ∧ (C.st x).IsL) := by
    intro x hx
    by_cases hxv : x = v
    · exact .inl hxv
    by_cases hxu : x = u
    · subst hxu; rw [hDu] at hx; exact absurd hx ha
    · exact .inr ⟨hxu, hxv, hDo x hxu hxv ▸ hx⟩
  refine ⟨fun x => ?_, ?_, fun x hx => ?_, fun x y hx hy hxy => ?_⟩
  · by_cases hxu : x = u
    · subst hxu
      rw [hDu, Protocol.deg_interact_activate_left huv he (by rw [hδ']), hdu, hC.dg]
    by_cases hxv : x = v
    · subst hxv
      rw [hDv, Protocol.deg_interact_activate_right huv he (by rw [hδ']), hdv, hC.dg]
    rw [hDo x hxu hxv, Protocol.deg_interact_other hxu hxv, hC.dg]
  · rw [hG]; exact (SimpleGraph.isAcyclic_add_edge_iff_of_not_reachable u v hnr).2 hC.acyclic
  · by_cases hxu : x = u
    · subst hxu; exact ⟨v, hDv ▸ hb, hadj.reachable⟩
    by_cases hxv : x = v
    · subst hxv; exact ⟨x, hDv ▸ hb, .rfl⟩
    rw [hDo x hxu hxv] at hx
    obtain ⟨y, hy, hxy⟩ := hC.cover x hx
    by_cases hyu : y = u
    · subst hyu; exact ⟨v, hDv ▸ hb, (hxy.mono hle).trans hadj.reachable⟩
    by_cases hyv : y = v
    · subst hyv; exact ⟨y, hDv ▸ hb, hxy.mono hle⟩
    · exact ⟨y, hDo y hyu hyv ▸ hy, hxy.mono hle⟩
  · rw [hG, SimpleGraph.reachable_sup_edge_iff] at hxy
    -- old leaders reachable from `v` (resp. `u`) are `v` (resp. `u`)
    have key : ∀ z, z = v ∨ (z ≠ u ∧ z ≠ v ∧ (C.st z).IsL) → ∀ t, (t = v ∨ (t ≠ u ∧ t ≠ v ∧
        (C.st t).IsL)) → C.active.Reachable z t → z = t := by
      rintro z (rfl | ⟨hzu, hzv, hz⟩) t (rfl | ⟨htu, htv, ht⟩) hzt
      · rfl
      · exact (hv t ht hzt).symm
      · exact hv z hz hzt.symm
      · exact hC.uniq z t hz ht hzt
    have hnu : ∀ z, z = v ∨ (z ≠ u ∧ z ≠ v ∧ (C.st z).IsL) → ¬ C.active.Reachable z u := by
      rintro z (rfl | ⟨hzu, -, hz⟩) hzu'
      · exact hnr hzu'.symm
      · exact hzu (hu z hz hzu'.symm)
    rcases hxy with h | ⟨h1, -⟩ | ⟨-, h2⟩
    · exact key x (hL x hx) y (hL y hy) h
    · exact absurd h1 (hnu x (hL x hx))
    · exact absurd h2.symm (hnu y (hL y hy))

/-- Preservation of the invariant when the leader `w` at `u` moves to its neighbour `v`. -/
theorem inv_move (hC : Inv C) (huv : u ≠ v) {a b : St}
    (hδ : δ (C.st u) (C.st v) (C.edge u v) = (a, b, true)) (he : C.edge u v = true)
    (hdu : a.dg = (C.st u).dg) (hdv : b.dg = (C.st v).dg) (ha : ¬ a.IsL) (hb : b.IsL)
    (hu : (C.st u).IsL) (hv : ¬ (C.st v).IsL) :
    Inv (P.interact C u v) := by
  have hδ' : P.δ (C.st u) (C.st v) (C.edge u v) = (a, b, true) := hδ
  have hDu : (P.interact C u v).st u = a := by rw [interact_st_eq, ite_eq_left rfl, hδ]
  have hDv : (P.interact C u v).st v = b := by
    rw [interact_st_eq, ite_eq_right (Ne.symm huv), ite_eq_left rfl, hδ]
  have hDo : ∀ x, x ≠ u → x ≠ v → (P.interact C u v).st x = C.st x :=
    fun x hxu hxv => Protocol.interact_st_other C hxu hxv
  have hG : (P.interact C u v).active = C.active :=
    Protocol.interact_active_of_edge_eq (by rw [hδ', he])
  have hadj : C.active.Adj u v := ⟨huv, he⟩
  have hL : ∀ x, ((P.interact C u v).st x).IsL → x = v ∨ (x ≠ u ∧ x ≠ v ∧ (C.st x).IsL) := by
    intro x hx
    by_cases hxv : x = v
    · exact .inl hxv
    by_cases hxu : x = u
    · subst hxu; rw [hDu] at hx; exact absurd hx ha
    · exact .inr ⟨hxu, hxv, hDo x hxu hxv ▸ hx⟩
  refine ⟨fun x => ?_, hG ▸ hC.acyclic, fun x hx => ?_, fun x y hx hy hxy => ?_⟩
  · rw [Protocol.deg_interact_of_edge_eq (by rw [hδ', he])]
    by_cases hxu : x = u
    · subst hxu; rw [hDu, hdu, hC.dg]
    by_cases hxv : x = v
    · subst hxv; rw [hDv, hdv, hC.dg]
    rw [hDo x hxu hxv, hC.dg]
  · rw [hG]
    by_cases hxu : x = u
    · subst hxu; exact ⟨v, hDv ▸ hb, hadj.reachable⟩
    by_cases hxv : x = v
    · subst hxv; exact ⟨x, hDv ▸ hb, .rfl⟩
    rw [hDo x hxu hxv] at hx
    obtain ⟨y, hy, hxy⟩ := hC.cover x hx
    by_cases hyu : y = u
    · subst hyu; exact ⟨v, hDv ▸ hb, hxy.trans hadj.reachable⟩
    have hyv : y ≠ v := by rintro rfl; exact hv hy
    exact ⟨y, hDo y hyu hyv ▸ hy, hxy⟩
  · rw [hG] at hxy
    have key : ∀ z, z = v ∨ (z ≠ u ∧ z ≠ v ∧ (C.st z).IsL) → ∀ t, (t = v ∨ (t ≠ u ∧ t ≠ v ∧
        (C.st t).IsL)) → C.active.Reachable z t → z = t := by
      rintro z (rfl | ⟨hzu, hzv, hz⟩) t (rfl | ⟨htu, htv, ht⟩) hzt
      · rfl
      · exact absurd (hC.uniq u t hu ht (hadj.reachable.trans hzt)).symm htu
      · exact absurd (hC.uniq u z hu hz (hadj.reachable.trans hzt.symm)).symm hzu
      · exact hC.uniq z t hz ht hzt
    exact key x (hL x hx) y (hL y hy) hxy

theorem inv_step {C D : Config V St} (hC : Inv C) (h : P.Step C D) : Inv D := by
  obtain ⟨u, v, huv, rfl⟩ := h
  have hlu : ∀ y, (C.st y).IsL → C.active.Reachable u y → (C.st u).IsL → y = u :=
    fun y hy h hu => (hC.uniq u y hu hy h).symm
  rcases δ_cases (C.st u) (C.st v) (C.edge u v) with h | ⟨hu, hv, he, h⟩ | ⟨hu, hv, he, h⟩ |
    ⟨hu, hv, he, h⟩ | ⟨hu, hv, he, h⟩ | ⟨hu, hv, he, h⟩
  · rw [Protocol.interact_eq_self C h]; exact hC
  · have hu0 := (st_eq_q0_iff hC).1 hu
    have hv0 := (st_eq_q0_iff hC).1 hv
    exact inv_activate hC huv h he (by simp [hu, St.dg]) (by simp [hv, St.dg]) (by simp [St.IsL])
      (by simp [St.IsL]) (fun h => huv (eq_of_reachable_deg_zero hv0 h))
      (fun y _ h => (eq_of_reachable_deg_zero hu0 h.symm)) (fun y _ h => (eq_of_reachable_deg_zero hv0 h.symm))
  · have hv0 := (st_eq_q0_iff hC).1 hv
    exact inv_activate hC huv h he (by simp [hu, St.dg]) (by simp [hv, St.dg]) (by simp [St.IsL])
      (by simp [St.IsL]) (fun h => huv (eq_of_reachable_deg_zero hv0 h))
      (fun y hy h => hlu y hy h (by simp [hu, St.IsL]))
      (fun y _ h => (eq_of_reachable_deg_zero hv0 h.symm))
  · have hul : (C.st u).IsL := by simp [hu, St.IsL]
    have hvl : (C.st v).IsL := by simp [hv, St.IsL]
    exact inv_activate hC huv h he (by simp [hu, St.dg]) (by simp [hv, St.dg]) (by simp [St.IsL])
      (by simp [St.IsL]) (fun h => huv (hC.uniq u v hul hvl h))
      (fun y hy h => hlu y hy h hul) (fun y hy h => (hC.uniq v y hvl hy h).symm)
  · exact inv_move hC huv h he (by simp [hu, St.dg]) (by simp [hv, St.dg]) (by simp [St.IsL])
      (by simp [St.IsL]) (by simp [hu, St.IsL]) (by simp [hv, St.IsL])
  · exact inv_move hC huv h he (by simp [hu, St.dg]) (by simp [hv, St.dg]) (by simp [St.IsL])
      (by simp [St.IsL]) (by simp [hu, St.IsL]) (by simp [hv, St.IsL])

theorem inv_reach {C D : Config V St} (hC : Inv C) (h : P.Reachable C D) : Inv D := by
  induction h with
  | refl => exact hC
  | tail _ hst ih => exact inv_step ih hst

end step

/-! ### Counting states -/

omit [DecidableEq V] in
/-- Counting agents in a set of states, when only two agents change state. -/
theorem card_filter_two [DecidableEq V] {f g : V → St} {u v : V} (huv : u ≠ v)
    (h : ∀ x, x ≠ u → x ≠ v → g x = f x) (p : St → Prop) [DecidablePred p] :
    (Finset.univ.filter fun x => p (g x)).card + (if p (f u) then 1 else 0) +
        (if p (f v) then 1 else 0) =
      (Finset.univ.filter fun x => p (f x)).card + (if p (g u) then 1 else 0) +
        (if p (g v) then 1 else 0) := by
  simp only [Finset.card_filter]
  have hv : v ∈ Finset.univ.erase u := Finset.mem_erase.2 ⟨Ne.symm huv, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u), ← Finset.add_sum_erase _ _ hv,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ u), ← Finset.add_sum_erase _ _ hv]
  have : ∑ x ∈ (Finset.univ.erase u).erase v, (if p (g x) then 1 else 0) =
      ∑ x ∈ (Finset.univ.erase u).erase v, (if p (f x) then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [Finset.mem_erase] at hx
    rw [h x hx.2.1 hx.1]
  rw [this]
  ring

/-- Number of leaders plus isolated agents (decreases at every activation). -/
def m1 (C : Config V St) : ℕ := (Finset.univ.filter fun x => (C.st x).IsL ∨ C.st x = q0).card

/-- Number of `w` leaders (decreases when a `w` reaches an endpoint). -/
def m2 (C : Config V St) : ℕ := (Finset.univ.filter fun x => C.st x = w).card

omit [Fintype V] [DecidableEq V] in
theorem active_eq_of_edge_eq {C D : Config V St} (h : D.edge = C.edge) : D.active = C.active := by
  ext x y; simp [Config.active_adj, h]

/-- The states of a leader-free agent of positive degree. -/
theorem st_of_not_isL {C : Config V St} (hC : Inv C) {y : V} (hy : ¬ (C.st y).IsL)
    (hd : C.deg y ≠ 0) : C.st y = q1 ∨ C.st y = q2 := by
  have := hC.dg y
  cases h : C.st y <;> simp_all [St.IsL, St.dg]

theorem deg_ne_zero_of_adj {C : Config V St} {x y : V} (h : C.active.Adj x y) : C.deg y ≠ 0 := by
  rw [Config.deg, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  exact ⟨x, by simp [h.1, C.symm y x, h.2]⟩

/-- An agent of degree 2 has a neighbour different from any given agent. -/
theorem exists_adj_ne {C : Config V St} {x : V} (hx : C.deg x = 2) (z : V) :
    ∃ y, C.active.Adj x y ∧ y ≠ z := by
  obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.1 hx
  have ha : a ∈ Finset.univ.filter fun v => v ≠ x ∧ C.edge x v = true := hs ▸ by simp
  have hb : b ∈ Finset.univ.filter fun v => v ≠ x ∧ C.edge x v = true := hs ▸ by simp
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_cases haz : a = z
  · exact ⟨b, ⟨Ne.symm hb.1, hb.2⟩, fun h => hab (haz.trans h.symm)⟩
  · exact ⟨a, ⟨Ne.symm ha.1, ha.2⟩, haz⟩

/-- A step `(w, ·, 1)` from `x` to its neighbour `y`: the new states. -/
theorem interact_wq {D : Config V St} {x y : V} (hxy : x ≠ y) {a b : St}
    (hδ : δ (D.st x) (D.st y) (D.edge x y) = (a, b, true)) :
    (P.interact D x y).st x = a ∧ (P.interact D x y).st y = b ∧
      ∀ z, z ≠ x → z ≠ y → (P.interact D x y).st z = D.st z :=
  ⟨by rw [interact_st_eq, ite_eq_left rfl, hδ],
   by rw [interact_st_eq, ite_eq_right (Ne.symm hxy), ite_eq_left rfl, hδ],
   fun z hzx hzy => Protocol.interact_st_other D hzx hzy⟩

/-- A `w` leader walks along its line to an endpoint and becomes `l` there. -/
theorem move_w {C : Config V St} (hC : Inv C) {u : V} (hu : C.st u = w) :
    ∃ E, P.Reachable C E ∧ m1 E = m1 C ∧ m2 E + 1 = m2 C := by
  suffices H : ∀ k, ∀ (D : Config V St) (x : V) (p : C.active.Walk u x), p.IsPath →
      Fintype.card V ≤ p.length + k → P.Reachable C D → D.edge = C.edge → m1 D = m1 C →
      m2 D = m2 C → D.st x = w → (∀ y ∈ p.support, y ≠ x → D.st y = q2) →
      (∀ y ∉ p.support, D.st y = C.st y) →
      ∃ E, P.Reachable C E ∧ m1 E = m1 C ∧ m2 E + 1 = m2 C from
    H (Fintype.card V) C u .nil (by simp) (by simp) .refl rfl rfl rfl hu (by simp) (fun _ _ => rfl)
  intro k
  induction k with
  | zero =>
    intro D x p hp hk
    exact absurd hp.length_lt (by omega)
  | succ k ih =>
    intro D x p hp hk hCD hDe h1 h2 hx hin hout
    have hD := inv_reach hC hCD
    have hDa : D.active = C.active := active_eq_of_edge_eq hDe
    have hdx : D.deg x = 2 := by rw [← hD.dg, hx]; rfl
    obtain ⟨y, hxy, hyp⟩ := exists_adj_ne hdx p.penultimate
    rw [hDa] at hxy
    have hyns : y ∉ p.support := fun hy => hyp (hC.acyclic.eq_penultimate_of_adj_end hp hxy hy)
    have hyC : D.st y = C.st y := hout y hyns
    have hyL : ¬ (C.st y).IsL := fun hL => hyns (by
      rw [← hC.uniq u y (by simp [hu, St.IsL]) hL (p.reachable.trans hxy.reachable)]
      exact p.start_mem_support)
    have hxy' : x ≠ y := hxy.1
    have hDxy : D.edge x y = true := by rw [hDe]; exact hxy.2
    rcases st_of_not_isL hC hyL (deg_ne_zero_of_adj hxy) with hy1 | hy2
    · -- the walk ends: `(w, q₁, 1) → (q₂, l, 1)`
      have hδ : δ (D.st x) (D.st y) (D.edge x y) = (q2, l, true) := by
        rw [hx, hyC, hy1, hDxy]; rfl
      obtain ⟨hEx, hEy, hEo⟩ := interact_wq hxy' hδ
      refine ⟨P.interact D x y, hCD.tail (Protocol.step_of_ne hxy'), ?_, ?_⟩
      · have := card_filter_two hxy' hEo (fun s => s.IsL ∨ s = q0)
        simp only [hEx, hEy, hx, hyC, hy1, St.IsL] at this
        simp only [m1, St.IsL] at h1 ⊢
        simp at this
        omega
      · have := card_filter_two hxy' hEo (fun s => s = w)
        simp only [hEx, hEy, hx, hyC, hy1] at this
        simp only [m2] at h2 ⊢
        simp at this
        omega
    · -- the walk continues: `(w, q₂, 1) → (q₂, w, 1)`
      have hδ : δ (D.st x) (D.st y) (D.edge x y) = (q2, w, true) := by
        rw [hx, hyC, hy2, hDxy]; rfl
      obtain ⟨hEx, hEy, hEo⟩ := interact_wq hxy' hδ
      refine ih (P.interact D x y) y (p.concat hxy) (hp.concat hyns hxy) (by simp; omega)
        (hCD.tail (Protocol.step_of_ne hxy')) ?_ ?_ ?_ hEy ?_ ?_
      · rw [Protocol.interact_edge_of_edge_eq (by show (δ _ _ _).2.2 = _; rw [hδ, hDxy]), hDe]
      · have := card_filter_two hxy' hEo (fun s => s.IsL ∨ s = q0)
        simp only [hEx, hEy, hx, hyC, hy2, St.IsL] at this
        simp only [m1, St.IsL] at h1 ⊢
        simp at this
        omega
      · have := card_filter_two hxy' hEo (fun s => s = w)
        simp only [hEx, hEy, hx, hyC, hy2] at this
        simp only [m2] at h2 ⊢
        simp at this
        omega
      · intro z hz hzy
        rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | hz
        · by_cases hzx : z = x
          · rw [hzx, hEx]
          · rw [hEo z hzx hzy]; exact hin z hz hzx
        · exact absurd hz hzy
      · intro z hz
        rw [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton, not_or] at hz
        have hzx : z ≠ x := fun h => hz.1 (h ▸ p.end_mem_support)
        rw [hEo z hzx hz.2]
        exact hout z hz.1

/-! ### Final configurations -/

/-- Final configurations: no isolated agent and a unique leader. -/
def Final (C : Config V St) : Prop :=
  Inv C ∧ (∀ u, C.st u ≠ q0) ∧ ∀ x y, (C.st x).IsL → (C.st y).IsL → x = y

theorem edge_false_of_q0 {C : Config V St} (hC : Inv C) {u v : V} (hvu : v ≠ u)
    (hu : C.st u = q0) : C.edge v u = false := by
  by_contra h
  exact deg_ne_zero_of_adj ⟨hvu, by simpa using h⟩ ((st_eq_q0_iff hC).1 hu)

/-- One round of the construction: decrease `(m1, m2)` lexicographically. -/
theorem reach_step (hn : 2 ≤ Fintype.card V) {C : Config V St} (hC : Inv C)
    (hnf : ¬ ((∀ u, C.st u ≠ q0) ∧ ∀ x y, (C.st x).IsL → (C.st y).IsL → x = y)) :
    ∃ D, P.Reachable C D ∧ Inv D ∧ toLex (m1 D, m2 D) < toLex (m1 C, m2 C) := by
  -- an activation step `(a, b, 0) → (a', b', 1)` from `x` to `y`
  have act : ∀ x y, x ≠ y → ∀ a b, δ (C.st x) (C.st y) (C.edge x y) = (a, b, true) →
      (if (C.st x).IsL ∨ C.st x = q0 then 1 else 0) + (if (C.st y).IsL ∨ C.st y = q0 then 1 else 0)
        = (if a.IsL ∨ a = q0 then 1 else 0) + (if b.IsL ∨ b = q0 then 1 else 0) + 1 →
      ∃ D, P.Reachable C D ∧ Inv D ∧ toLex (m1 D, m2 D) < toLex (m1 C, m2 C) := by
    intro x y hxy a b hδ hcnt
    obtain ⟨hEx, hEy, hEo⟩ := interact_wq hxy hδ
    refine ⟨P.interact C x y, Protocol.reachable_of_ne hxy, inv_step hC (Protocol.step_of_ne hxy),
      Prod.Lex.toLex_lt_toLex.2 (.inl ?_)⟩
    have := card_filter_two hxy hEo (fun s => s.IsL ∨ s = q0)
    simp only [hEx, hEy] at this
    simp only [m1]
    omega
  by_cases hw : ∃ u, C.st u = w
  · obtain ⟨u, hu⟩ := hw
    obtain ⟨E, hCE, h1, h2⟩ := move_w hC hu
    exact ⟨E, hCE, inv_reach hC hCE, Prod.Lex.toLex_lt_toLex.2 (.inr ⟨h1, by omega⟩)⟩
  push Not at hw
  have hLl : ∀ x, (C.st x).IsL → C.st x = l := fun x hx => hx.resolve_right (hw x)
  by_cases h0 : ∃ u, C.st u = q0
  · obtain ⟨u, hu⟩ := h0
    by_cases hL : ∃ x, (C.st x).IsL
    · obtain ⟨x, hx⟩ := hL
      have hxl := hLl x hx
      have hxu : x ≠ u := by rintro rfl; rw [hu] at hxl; exact absurd hxl (by decide)
      exact act x u hxu q2 l (by rw [hxl, hu, edge_false_of_q0 hC hxu hu]; rfl)
        (by rw [hxl, hu]; decide)
    · push Not at hL
      obtain ⟨v, hvu⟩ := Fintype.exists_ne_of_one_lt_card (by omega) u
      have hv : C.st v = q0 := by
        by_contra hv
        obtain ⟨y, hy, -⟩ := hC.cover v hv
        exact hL y hy
      exact act u v (Ne.symm hvu) q1 l (by rw [hu, hv, edge_false_of_q0 hC (Ne.symm hvu) hv]; rfl)
        (by rw [hu, hv]; decide)
  · push Not at h0
    have : ¬ ∀ x y, (C.st x).IsL → (C.st y).IsL → x = y := fun h => hnf ⟨h0, h⟩
    push Not at this
    obtain ⟨x, y, hx, hy, hxy⟩ := this
    have hxl := hLl x hx
    have hyl := hLl y hy
    have he : C.edge x y = false := by
      by_contra he
      exact hxy (hC.uniq x y hx hy (SimpleGraph.Adj.reachable ⟨hxy, by simpa using he⟩))
    exact act x y hxy q2 w (by rw [hxl, hyl, he]; rfl) (by rw [hxl, hyl]; decide)

theorem reach_final (hn : 2 ≤ Fintype.card V) {C : Config V St} (hC : Inv C) :
    ∃ D, P.Reachable C D ∧ Final D := by
  obtain ⟨D, hCD, hD, h⟩ := exists_reach_of_measure (R := P.Step) Inv
    (fun D => (∀ u, D.st u ≠ q0) ∧ ∀ x y, (D.st x).IsL → (D.st y).IsL → x = y)
    (fun D => toLex (m1 D, m2 D)) (fun D hD hnf => reach_step hn hD hnf) C hC
  exact ⟨D, hCD, hD, h⟩

/-- In a final configuration only the leader moves: the edges do not change and the
configuration stays final. -/
theorem final_step {C D : Config V St} (hC : Final C) (h : P.Step C D) :
    D.edge = C.edge ∧ Final D := by
  obtain ⟨hI, h0, h1⟩ := hC
  obtain ⟨u, v, huv, rfl⟩ := h
  have hD := inv_step hI (Protocol.step_of_ne huv)
  rcases δ_cases (C.st u) (C.st v) (C.edge u v) with h | ⟨hu, -⟩ | ⟨-, hv, -⟩ |
    ⟨hu, hv, -⟩ | ⟨hu, hv, he, h⟩ | ⟨hu, hv, he, h⟩
  · rw [Protocol.interact_eq_self C h]; exact ⟨rfl, hI, h0, h1⟩
  · exact absurd hu (h0 u)
  · exact absurd hv (h0 v)
  · exact absurd (h1 u v (by simp [hu, St.IsL]) (by simp [hv, St.IsL])) huv
  all_goals
    obtain ⟨hEx, hEy, hEo⟩ := interact_wq huv h
    refine ⟨Protocol.interact_edge_of_edge_eq (by show (δ _ _ _).2.2 = _; rw [h, he]), hD,
      fun x => ?_, fun x y hx hy => ?_⟩
    · by_cases hxu : x = u
      · rw [hxu, hEx]; decide
      by_cases hxv : x = v
      · rw [hxv, hEy]; decide
      rw [hEo x hxu hxv]; exact h0 x
    · have key : ∀ z, ((P.interact C u v).st z).IsL → z = v := by
        intro z hz
        by_contra hzv
        by_cases hzu : z = u
        · rw [hzu, hEx] at hz; exact absurd hz (by decide)
        rw [hEo z hzu hzv] at hz
        exact hzu (h1 z u hz (by simp [hu, St.IsL]))
      rw [key x hx, key y hy]

/-- The active graph of a final configuration is a spanning line. -/
theorem final_spanningLine (hn : 2 ≤ Fintype.card V) {C : Config V St} (hC : Final C) :
    IsSpanningLine (P.output C) := by
  obtain ⟨hI, h0, h1⟩ := hC
  have hout : ∀ q, P.out q = true := fun _ => rfl
  obtain ⟨a⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨x₀, hx₀, -⟩ := hI.cover a (h0 a)
  have hconn : C.active.Connected := by
    refine SimpleGraph.connected_iff_exists_forall_reachable _ |>.2 ⟨x₀, fun v => ?_⟩
    obtain ⟨y, hy, hvy⟩ := hI.cover v (h0 v)
    rw [h1 y x₀ hy hx₀] at hvy
    exact hvy.symm
  refine isSpanningLine_output hout hconn hI.acyclic fun v => ?_
  rw [← hI.dg]; have := h0 v; cases h : C.st v <;> simp_all [St.dg]

/-- **Theorem 3 (correctness) of Michail–Spirakis.** For every number `n ≥ 2` of agents, Protocol
Simple-Global-Line constructs a spanning line under every globally fair scheduler. -/
theorem constructs_spanningLine (hn : 2 ≤ Fintype.card V) :
    P.Constructs (V := V) IsSpanningLine := by
  refine P.constructs_of_reach {C | Final C} (fun C D hC hCD => (final_step hC hCD).2)
    (fun C D hC hCD => ?_) (fun C hC => final_spanningLine hn hC) (fun C hC => ?_)
  · exact P.output_eq_of (fun _ => rfl) (final_step hC hCD).1
  · obtain ⟨D, hCD, hD⟩ := reach_final hn (inv_reach inv_init hC)
    exact ⟨D, hD, hCD⟩

end Podc.NetworkConstructors.SimpleLine
