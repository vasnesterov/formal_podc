import Papers.PODC2014.NetworkConstructors.CliquesStep

/-!
# Protocol 9 (`c`-Cliques): reaching a stable configuration

From every configuration satisfying the invariant, the scheduler can reach a configuration in which

1. no `f_j` is left (`f_j`s release their followers, deepest first);
2. at most one partial leader `l_i` is left (repeatedly, a partial leader of maximal index absorbs
   another partial leader, whose followers are then released);
3. no `l̄_i` is left (counting leaders number their followers);
4. no `r` is left (tokens return to their leaders);
5. no wrong edge is left (for a wrong edge `xy`, both leaders visit `x` and `y`, cut `xy`, and
   return);
6. every numbered follower has number `c − 1` (missing edges inside components are added).
-/

namespace Podc.NetworkConstructors.Cliques

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem St

variable {c : ℕ} {hc : 3 ≤ c} {V : Type*} [Fintype V] [DecidableEq V]
  {C : Config V (St c)} {p : V → V} {ht : V → ℕ}

/-! ### Phase predicates and measures -/

/-- The state `l_0`. -/
abbrev l0 : St c := .l 0 (Nat.zero_le _)

/-- No `f_j` is left. -/
def NoFi (C : Config V (St c)) : Prop := ∀ x, (C.st x).isFi = false

/-- At most one partial leader `l_i`. -/
def OnePartial (C : Config V (St c)) : Prop :=
  ∀ x y, (C.st x).isL = true → (C.st y).isL = true → x = y

/-- No counting leader `l̄_i` is left. -/
def NoLbar (C : Config V (St c)) : Prop := ∀ x, (C.st x).isLbar = false

/-- No `r` is left. -/
def NoR (C : Config V (St c)) : Prop := ∀ x, C.st x ≠ .r

/-- No wrong edge: active edges between numbered followers join children of the same leader. -/
def NoWrong (C : Config V (St c)) (p : V → V) : Prop :=
  ∀ x y, x ≠ y → (C.st x).isFol = true → (C.st y).isFol = true → C.edge x y = true → p x = p y

/-- All numbered followers have number `c − 1`. -/
def Full (C : Config V (St c)) : Prop := ∀ x, (C.st x).isFol = true → (C.st x).idx = c - 1

/-- Pending releases: `f_j ↦ j`. -/
def wFi : St c → ℕ
  | fi j _ _ => j
  | _ => 0

/-- Agents of partial components (and pending releases): `l_i ↦ i + 1`, `f_j ↦ j`. -/
def wW : St c → ℕ
  | l i _ => i + 1
  | fi j _ _ => j
  | _ => 0

/-- The index of a partial leader. -/
def lidx : St c → ℕ
  | l i _ => i
  | _ => 0

/-- Followers still to be numbered: `l̄_i ↦ c − 1 − i`. -/
def wLbar : St c → ℕ
  | lbar i _ => c - 1 - i
  | _ => 0

/-- `r ↦ 1`. -/
def wR : St c → ℕ
  | r => 1
  | _ => 0

/-- Missing edges: `k ↦ c − 1 − k`. -/
def wMiss : St c → ℕ
  | num k _ _ => c - 1 - k
  | St.lp k _ _ => c - 1 - k
  | _ => 0

/-- Sum of a weight over all agents. -/
def wsum (w : St c → ℕ) (C : Config V (St c)) : ℕ := ∑ x, w (C.st x)

omit [DecidableEq V] in
theorem wsum_change {w : St c → ℕ} {C D : Config V (St c)} {u v : V} (huv : u ≠ v)
    (h : ∀ z, z ≠ u → z ≠ v → D.st z = C.st z) :
    wsum w D + w (C.st u) + w (C.st v) = wsum w C + w (D.st u) + w (D.st v) := by
  classical
  unfold wsum
  have hv : v ∈ Finset.univ.erase u := Finset.mem_erase.2 ⟨Ne.symm huv, Finset.mem_univ _⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u), ← Finset.add_sum_erase _ _ hv,
    ← Finset.add_sum_erase _ (fun x => w (C.st x)) (Finset.mem_univ u),
    ← Finset.add_sum_erase _ (fun x => w (C.st x)) hv]
  have : ∑ x ∈ (Finset.univ.erase u).erase v, w (D.st x) =
      ∑ x ∈ (Finset.univ.erase u).erase v, w (C.st x) := by
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [h z (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz)) (Finset.ne_of_mem_erase hz)]
  rw [this]; ring

/-- Reaching a goal by a measure that decreases unless the goal is reached. -/
theorem reach_good {X : Type*} {R : X → X → Prop} (I good : X → Prop) (f : X → ℕ)
    (h : ∀ x, I x → ¬ good x → ∃ y, Reach R x y ∧ I y ∧ (good y ∨ f y < f x)) :
    ∀ x, I x → ∃ y, Reach R x y ∧ I y ∧ good y := by
  classical
  refine exists_reach_of_measure I good (fun x => if good x then 0 else f x + 1) fun x hx hg => ?_
  obtain ⟨y, hxy, hy, h'⟩ := h x hx hg
  refine ⟨y, hxy, hy, ?_⟩
  simp only [hg, ite_false]
  split_ifs with hgy
  · omega
  · rcases h' with h' | h'
    · exact absurd h' hgy
    · omega

theorem st_eq_fi {q : St c} (h : q.isFi = true) : ∃ j h1 h2, q = .fi j h1 h2 := by
  cases q <;> simp_all [isFi]

theorem st_eq_l {q : St c} (h : q.isL = true) : ∃ i hi, q = .l i hi := by
  cases q <;> simp_all [isL]

theorem st_eq_lbar {q : St c} (h : q.isLbar = true) : ∃ i hi, q = .lbar i hi := by
  cases q <;> simp_all [isLbar]

/-- A non-root, non-numbered state is `f` or `f_j`. -/
theorem st_f_or_fi {q : St c} (h1 : q.isRoot = false) (h2 : q.isFol = false) :
    q = .f ∨ q.isFi = true := by
  cases q <;> simp_all [isRoot, isFol, isFi]

/-! ### Phase 1: releasing -/

/-- States change only at `f`/`f_j` agents, and only to `f`, `l_0`, `f_j`. -/
def Track (C₀ C : Config V (St c)) : Prop :=
  ∀ x, (C₀.st x ≠ .f → (C₀.st x).isFi = false → C.st x = C₀.st x) ∧
    (C.st x = C₀.st x ∨ C.st x = .f ∨ C.st x = l0 ∨ (C.st x).isFi = true)

omit [Fintype V] [DecidableEq V] in
theorem Track.refl (C : Config V (St c)) : Track C C := fun _ => ⟨fun _ _ => rfl, .inl rfl⟩

omit [Fintype V] [DecidableEq V] in
theorem Track.f_or_fi {C₀ C : Config V (St c)} (hT : Track C₀ C) {x : V}
    (h : C.st x = .f ∨ (C.st x).isFi = true) : C₀.st x = .f ∨ (C₀.st x).isFi = true := by
  by_contra hn
  push Not at hn
  rw [(hT x).1 hn.1 (by simpa using hn.2)] at h
  rcases h with h | h
  · exact hn.1 h
  · exact hn.2 h

/-- One release step. -/
theorem release_step (hI : Inv C p ht) {x w : V} (hxw : x ≠ w) {j h1 h2}
    (hx : C.st x = .fi j h1 h2) (hw : C.st w = .f) (he : C.edge x w = true) :
    let D := (cliques c hc).interact C x w
    Inv D (Function.update p w w) ht ∧ (D.st x = .f ∨ (D.st x).isFi = true) ∧ D.st w = l0 ∧
      (∀ z, z ≠ x → z ≠ w → D.st z = C.st z) ∧ wsum wW D = wsum wW C ∧
      wsum wFi D < wsum wFi C := by
  intro D
  have hDx : D.st x = if h : 1 < j then .fi (j - 1) (by omega) (by omega) else .f := by
    simp [D, hx, hw, he, δ]
  have hDw : D.st w = l0 := by simp [D, Protocol.interact_st_right C hxw, hx, hw, he, δ]
  have hDo : ∀ z, z ≠ x → z ≠ w → D.st z = C.st z := fun z h1 h2 =>
    Protocol.interact_st_other C h1 h2
  have h1 := wsum_change (w := wW) hxw hDo
  have h2 := wsum_change (w := wFi) hxw hDo
  rw [hx, hw, hDw, hDx] at h1 h2
  refine ⟨hI.release hxw hx hw he, ?_, hDw, hDo, ?_, ?_⟩
  · rw [hDx]; split_ifs <;> simp [isFi]
  · split_ifs at h1 with hj <;> simp [wW] at h1 <;> omega
  · split_ifs at h2 with hj <;> simp [wFi] at h2 <;> omega

omit [Fintype V] [DecidableEq V] in
theorem track_clause {C₀ : Config V (St c)} {x : V} {q : St c}
    (h0 : C₀.st x = .f ∨ (C₀.st x).isFi = true)
    (h : q = C₀.st x ∨ q = .f ∨ q = l0 ∨ q.isFi = true) :
    (C₀.st x ≠ .f → (C₀.st x).isFi = false → q = C₀.st x) ∧
      (q = C₀.st x ∨ q = .f ∨ q = l0 ∨ q.isFi = true) := by
  refine ⟨fun h1 h2 => ?_, h⟩
  rcases h0 with h0 | h0
  · exact absurd h0 h1
  · rw [h0] at h2; exact absurd h2 (by simp)

/-- **Phase 1.** All pending releases can be completed. -/
theorem release_all (C : Config V (St c)) (hC : ∃ p ht, Inv C p ht) :
    ∃ D, (cliques c hc).Reachable C D ∧ (∃ p ht, Inv D p ht) ∧ NoFi D ∧ Track C D ∧
      wsum wW D = wsum wW C := by
  have key := reach_good (R := (cliques c hc).Step)
    (fun D => (∃ p ht, Inv D p ht) ∧ Track C D ∧ wsum wW D = wsum wW C) NoFi (wsum wFi) ?_ C
    ⟨hC, Track.refl C, rfl⟩
  · obtain ⟨D, hCD, ⟨hI, hT, hW⟩, hg⟩ := key
    exact ⟨D, hCD, hI, hg, hT, hW⟩
  rintro D ⟨⟨p, ht, hI⟩, hT, hW⟩ hg
  simp only [NoFi, not_forall] at hg
  set F := Finset.univ.filter fun x => (D.st x).isFi = true with hFdef
  have hF : F.Nonempty := by obtain ⟨x, hx⟩ := hg; exact ⟨x, by simpa [F] using hx⟩
  obtain ⟨x, hxF, hmin⟩ := F.exists_min_image ht hF
  obtain ⟨j, h1, h2, hx⟩ := st_eq_fi (by simpa [F] using hxF)
  have hk : 0 < (kids p x).card := by rw [hI.nkids, hx]; simp [St.nkids]; omega
  obtain ⟨w, hw⟩ := Finset.card_pos.1 hk
  have hw' := mem_kids.1 hw
  have hpw : p w ≠ w := by rw [hw'.1]; exact Ne.symm hw'.2
  have hwroot : (D.st w).isRoot = false := by
    cases h : (D.st w).isRoot
    · rfl
    · exact absurd ((hI.root w).2 h) hpw
  have hwfol : (D.st w).isFol = false := hI.not_fol_kids x (by simp [hx, St.nfol]) w hw
  have hwf : D.st w = .f := by
    rcases st_f_or_fi hwroot hwfol with h | h
    · exact h
    · exfalso
      have hlt := hI.ht_lt w hpw
      rw [hw'.1] at hlt
      have := hmin w (by simpa [F] using h)
      omega
  have hxw : x ≠ w := Ne.symm hw'.2
  have he : D.edge x w = true :=
    (hI.edge x w hxw (by simp [hx, St.isFol])).2 (.inr hw'.1)
  obtain ⟨hI', hDx, hDw, hDo, hW', hlt⟩ := release_step (hc := hc) hI hxw hx hwf he
  refine ⟨_, Relation.ReflTransGen.single (Protocol.step_of_ne hxw), ⟨⟨_, _, hI'⟩, ?_,
    hW'.trans hW⟩, .inr hlt⟩
  intro z
  by_cases hzx : z = x
  · subst hzx
    refine track_clause (hT.f_or_fi (.inr (by simp [hx, St.isFi]))) ?_
    rcases hDx with h | h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inr h))
  by_cases hzw : z = w
  · subst hzw
    exact track_clause (hT.f_or_fi (.inl hwf)) (.inr (.inr (.inl hDw)))
  rw [hDo z hzx hzw]; exact hT z

/-! ### Phase 2: merging partial components -/

/-- `u` is a partial leader of maximal index. -/
def IsMaxL (u : V) (C : Config V (St c)) : Prop :=
  ∃ i hi, C.st u = .l i hi ∧ ∀ y, (C.st y).isL = true → lidx (C.st y) ≤ i

omit [Fintype V] in
theorem interact_states {C : Config V (St c)} {u w : V} (huw : u ≠ w) :
    ((cliques c hc).interact C u w).st u = (δ c hc (C.st u) (C.st w) (C.edge u w)).1 ∧
    ((cliques c hc).interact C u w).st w = (δ c hc (C.st u) (C.st w) (C.edge u w)).2.1 ∧
    ∀ z, z ≠ u → z ≠ w → ((cliques c hc).interact C u w).st z = C.st z :=
  ⟨by simp, by simp [Protocol.interact_st_right C huw],
    fun _ h1 h2 => Protocol.interact_st_other C h1 h2⟩

omit [Fintype V] in
theorem noFi_of_change {C D : Config V (St c)} {u w : V} (hC : NoFi C)
    (hD : ∀ z, z ≠ u → z ≠ w → D.st z = C.st z) (hu : (D.st u).isFi = false)
    (hw : (D.st w).isFi = false) : NoFi D := by
  intro z
  by_cases hzu : z = u
  · subst hzu; exact hu
  by_cases hzw : z = w
  · subst hzw; exact hw
  rw [hD z hzu hzw]; exact hC z

/-- **Phase 2, inner loop.** A partial leader `u` of maximal index absorbs the other partial
leaders until it completes its component (then `wsum wW` drops) or it is the only one. -/
theorem absorb_all (W₀ : ℕ) (u : V) (C : Config V (St c))
    (hC : (∃ p ht, Inv C p ht) ∧ NoFi C ∧ wsum wW C ≤ W₀ ∧ (wsum wW C < W₀ ∨ IsMaxL u C)) :
    ∃ D, (cliques c hc).Reachable C D ∧ (OnePartial D ∨ wsum wW D < W₀) ∧
      (∃ p ht, Inv D p ht) ∧ NoFi D := by
  have key := reach_good (R := (cliques c hc).Step)
    (fun D => (∃ p ht, Inv D p ht) ∧ NoFi D ∧ wsum wW D ≤ W₀ ∧ (wsum wW D < W₀ ∨ IsMaxL u D))
    (fun D => OnePartial D ∨ wsum wW D < W₀) (fun D => c - lidx (D.st u)) ?_ C hC
  · obtain ⟨D, hCD, ⟨hI, hF, -⟩, hg⟩ := key
    exact ⟨D, hCD, hg, hI, hF⟩
  rintro C ⟨⟨p, ht, hI⟩, hF, hle, hmax⟩ hg
  simp only [not_or] at hg
  obtain ⟨hOP, hW⟩ := hg
  rcases hmax with hmax | ⟨i, hi, hu, hmax⟩
  · exact absurd hmax hW
  have hW0 : wsum wW C = W₀ := by omega
  -- another partial leader
  obtain ⟨w, hwu, hwL⟩ : ∃ w, w ≠ u ∧ (C.st w).isL = true := by
    simp only [OnePartial, not_forall] at hOP
    obtain ⟨x, y, hx, hy, hxy⟩ := hOP
    by_cases hxu : x = u
    · exact ⟨y, fun h => hxy (hxu.trans h.symm), hy⟩
    · exact ⟨x, hxu, hx⟩
  obtain ⟨j, hj, hw⟩ := st_eq_l hwL
  have hji : j ≤ i := by simpa [hw, lidx] using hmax w hwL
  have huw : u ≠ w := Ne.symm hwu
  have hpu : p u = u := hI.p_eq (by simp [hu, St.isRoot])
  have hpw : p w = w := hI.p_eq (by simp [hw, St.isRoot])
  have he : C.edge u w = false := by
    cases h : C.edge u w
    · rfl
    · rcases (hI.edge u w huw (by simp [hu, St.isFol])).1 h with h' | h'
      · exact absurd (hpu.symm.trans h') huw
      · exact absurd (hpw.symm.trans h') hwu
  obtain ⟨p', ht', hI'⟩ := hI.step (hc := hc) huw
  obtain ⟨hDu, hDw, hDo⟩ := interact_states (hc := hc) (C := C) huw
  rw [hu, hw, he] at hDu hDw
  have hWc := wsum_change (w := wW) huw hDo
  have hstep : (cliques c hc).Reachable C ((cliques c hc).interact C u w) :=
    Protocol.reachable_of_ne huw
  set D := (cliques c hc).interact C u w with hD
  by_cases h : i < c - 2 <;> by_cases h0 : j = 0
  · -- `(l_i, l_0, 0) → (l_{i+1}, f, 1)`
    subst h0
    simp only [δ, hji, h, ite_true, dite_true] at hDu hDw
    rw [hu, hw, hDu, hDw] at hWc
    simp only [wW] at hWc
    have hFD : NoFi D := noFi_of_change hF hDo (by rw [hDu]; rfl) (by rw [hDw]; rfl)
    refine ⟨D, hstep, ⟨⟨p', ht', hI'⟩, hFD, by omega, .inr ⟨i + 1, by omega, hDu, fun y hy => ?_⟩⟩,
      .inr (by rw [hDu, hu]; simp only [lidx]; omega)⟩
    by_cases hyu : y = u
    · subst hyu; rw [hDu]; simp [lidx]
    by_cases hyw : y = w
    · subst hyw; rw [hDw] at hy; simp [St.isL] at hy
    rw [hDo y hyu hyw] at hy ⊢
    exact (hmax y hy).trans (Nat.le_succ i)
  · -- `(l_i, l_j, 0) → (l_{i+1}, f_j, 1)`, then release
    simp only [δ, hji, h, h0, ite_true, dite_true, dite_false] at hDu hDw
    rw [hu, hw, hDu, hDw] at hWc
    simp only [wW] at hWc
    obtain ⟨E, hDE, hIE, hFE, hT, hWE⟩ := release_all (hc := hc) D ⟨p', ht', hI'⟩
    have hEu : E.st u = D.st u := (hT u).1 (by rw [hDu]; simp) (by rw [hDu]; rfl)
    refine ⟨E, hstep.trans hDE, ⟨hIE, hFE, by omega,
      .inr ⟨i + 1, by omega, hEu.trans hDu, fun y hy => ?_⟩⟩,
      .inr (by rw [hEu, hDu, hu]; simp only [lidx]; omega)⟩
    rcases (hT y).2 with h1 | h1 | h1 | h1
    · rw [h1] at hy ⊢
      by_cases hyu : y = u
      · subst hyu; rw [hDu]; simp [lidx]
      by_cases hyw : y = w
      · subst hyw; rw [hDw] at hy; simp [St.isL] at hy
      rw [hDo y hyu hyw] at hy ⊢
      exact (hmax y hy).trans (Nat.le_succ i)
    · rw [h1] at hy; simp [St.isL] at hy
    · rw [h1]; simp [lidx]
    · obtain ⟨_, _, _, h2⟩ := st_eq_fi h1; rw [h2] at hy; simp [St.isL] at hy
  · -- `(l_{c−2}, l_0, 0) → (l̄_1, 1, 1)`
    subst h0
    simp only [δ, hji, h, ite_true, dite_true, dite_false] at hDu hDw
    rw [hu, hw, hDu, hDw] at hWc
    simp only [wW] at hWc
    have hFD : NoFi D := noFi_of_change hF hDo (by rw [hDu]; rfl) (by rw [hDw]; rfl)
    have hlt : wsum wW D < W₀ := by omega
    exact ⟨D, hstep, ⟨⟨p', ht', hI'⟩, hFD, hlt.le, .inl hlt⟩, .inl (.inr hlt)⟩
  · -- `(l_{c−2}, l_j, 0) → (l̄_0, f_j, 1)`, then release
    simp only [δ, hji, h, h0, ite_true, dite_false] at hDu hDw
    rw [hu, hw, hDu, hDw] at hWc
    simp only [wW] at hWc
    obtain ⟨E, hDE, hIE, hFE, -, hWE⟩ := release_all (hc := hc) D ⟨p', ht', hI'⟩
    have hlt : wsum wW E < W₀ := by omega
    exact ⟨E, hstep.trans hDE, ⟨hIE, hFE, hlt.le, .inl hlt⟩, .inl (.inr hlt)⟩

/-- **Phase 2.** At most one partial leader can be left. -/
theorem merge_all (C : Config V (St c)) (hC : (∃ p ht, Inv C p ht) ∧ NoFi C) :
    ∃ D, (cliques c hc).Reachable C D ∧ ((∃ p ht, Inv D p ht) ∧ NoFi D) ∧ OnePartial D := by
  refine reach_good (R := (cliques c hc).Step) (fun D => (∃ p ht, Inv D p ht) ∧ NoFi D)
    OnePartial (wsum wW) ?_ C hC
  rintro C ⟨hI, hF⟩ hOP
  have hne : (Finset.univ.filter fun x => (C.st x).isL = true).Nonempty := by
    simp only [OnePartial, not_forall] at hOP
    obtain ⟨x, _, hx, _⟩ := hOP
    exact ⟨x, by simpa using hx⟩
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image _ (fun x => lidx (C.st x)) hne
  obtain ⟨i, hi, hui⟩ := st_eq_l (by simpa using hu)
  obtain ⟨D, hCD, hg, hID, hFD⟩ := absorb_all (hc := hc) (wsum wW C) u C
    ⟨hI, hF, le_rfl, .inr ⟨i, hi, hui, fun y hy => by
      simpa [hui, lidx] using hmax y (by simpa using hy)⟩⟩
  exact ⟨D, hCD, ⟨hID, hFD⟩, hg⟩

/-! ### Phases 3 and 4: counting and returning tokens -/

omit [Fintype V] in
theorem forall_of_change {P : St c → Prop} {C D : Config V (St c)} {u w : V}
    (hC : ∀ z, P (C.st z)) (hD : ∀ z, z ≠ u → z ≠ w → D.st z = C.st z) (hu : P (D.st u))
    (hw : P (D.st w)) : ∀ z, P (D.st z) := by
  intro z
  by_cases hzu : z = u
  · subst hzu; exact hu
  by_cases hzw : z = w
  · subst hzw; exact hw
  rw [hD z hzu hzw]; exact hC z

omit [Fintype V] [DecidableEq V] in
theorem onePartial_of_change {C D : Config V (St c)} {u w : V} (hC : OnePartial C)
    (hD : ∀ z, z ≠ u → z ≠ w → D.st z = C.st z) (hu : (D.st u).isL = false)
    (hw : (D.st w).isL = false) : OnePartial D := by
  intro x y hx hy
  have h : ∀ z, (D.st z).isL = true → z ≠ u ∧ z ≠ w := fun z hz =>
    ⟨fun h => by subst h; rw [hu] at hz; exact Bool.noConfusion hz,
      fun h => by subst h; rw [hw] at hz; exact Bool.noConfusion hz⟩
  obtain ⟨hxu, hxw⟩ := h x hx
  obtain ⟨hyu, hyw⟩ := h y hy
  rw [hD x hxu hxw] at hx
  rw [hD y hyu hyw] at hy
  exact hC x y hx hy

theorem st_eq_lp {q : St c} (h : q.isVis = true) : ∃ k h1 h2, q = .lp k h1 h2 := by
  cases q <;> simp_all [isVis]

/-- **Phase 3.** All counting leaders complete their numbering. -/
theorem count_all (C : Config V (St c)) (hC : Inv C p ht ∧ NoFi C ∧ OnePartial C) :
    ∃ D, (cliques c hc).Reachable C D ∧ (Inv D p ht ∧ NoFi D ∧ OnePartial D) ∧ NoLbar D := by
  refine reach_good (R := (cliques c hc).Step) (fun D => Inv D p ht ∧ NoFi D ∧ OnePartial D)
    NoLbar (wsum wLbar) ?_ C hC
  rintro C ⟨hI, hF, hO⟩ hg
  simp only [NoLbar, not_forall] at hg
  obtain ⟨u, hu⟩ := hg
  obtain ⟨i, hi, hu⟩ := st_eq_lbar (by simpa using hu)
  have hcard := Finset.card_filter_add_card_filter_not (s := kids p u)
    (fun w => (C.st w).isFol = true)
  rw [hI.nfol, hI.nkids, hu] at hcard
  simp only [St.nfol, St.nkids] at hcard
  obtain ⟨w, hw⟩ : ((kids p u).filter fun w => ¬(C.st w).isFol = true).Nonempty := by
    rw [← Finset.card_pos]; omega
  rw [Finset.mem_filter] at hw
  have hw' := mem_kids.1 hw.1
  have hpw : p w ≠ w := by rw [hw'.1]; exact Ne.symm hw'.2
  have hwroot : (C.st w).isRoot = false := by
    cases h : (C.st w).isRoot
    · rfl
    · exact absurd ((hI.root w).2 h) hpw
  have hwf : C.st w = .f := by
    rcases st_f_or_fi hwroot (by simpa using hw.2) with h | h
    · exact h
    · rw [hF w] at h; exact absurd h (by simp)
  have huw : u ≠ w := Ne.symm hw'.2
  have he : C.edge u w = true := (hI.edge u w huw (by simp [hu, St.isFol])).2 (.inr hw'.1)
  have hI' := hI.count (hc := hc) huw hu hwf he
  obtain ⟨hDu, hDw, hDo⟩ := interact_states (hc := hc) (C := C) huw
  rw [hu, hwf, he] at hDu hDw
  simp only [δ] at hDu hDw
  have hWc := wsum_change (w := wLbar) huw hDo
  rw [hu, hwf, hDu, hDw] at hWc
  refine ⟨_, Protocol.reachable_of_ne huw, ⟨hI', forall_of_change (P := fun q => q.isFi = false) hF hDo ?_ ?_,
    onePartial_of_change hO hDo ?_ ?_⟩, .inr ?_⟩
  · rw [hDu]; split_ifs <;> rfl
  · rw [hDw]; rfl
  · rw [hDu]; split_ifs <;> rfl
  · rw [hDw]; rfl
  · split_ifs at hWc with h <;> simp only [wLbar] at hWc <;> omega

/-- **Phase 4.** All tokens return to their leaders. -/
theorem return_all (C : Config V (St c))
    (hC : Inv C p ht ∧ NoFi C ∧ OnePartial C ∧ NoLbar C) :
    ∃ D, (cliques c hc).Reachable C D ∧ (Inv D p ht ∧ NoFi D ∧ OnePartial D ∧ NoLbar D) ∧
      NoR D := by
  refine reach_good (R := (cliques c hc).Step)
    (fun D => Inv D p ht ∧ NoFi D ∧ OnePartial D ∧ NoLbar D) NoR (wsum wR) ?_ C hC
  rintro C ⟨hI, hF, hO, hL⟩ hg
  simp only [NoR, not_forall, not_not] at hg
  obtain ⟨u, hu⟩ := hg
  have hcard := hI.nvis u
  rw [hu] at hcard
  simp only [St.nvis] at hcard
  obtain ⟨w, hw⟩ : ((kids p u).filter fun w => (C.st w).isVis = true).Nonempty := by
    rw [← Finset.card_pos]; omega
  rw [Finset.mem_filter] at hw
  have hw' := mem_kids.1 hw.1
  obtain ⟨k, h1, h2, hwk⟩ := st_eq_lp hw.2
  have hwu : w ≠ u := hw'.2
  have he : C.edge w u = true := by
    rw [C.symm]; exact (hI.edge u w (Ne.symm hwu) (by simp [hu, St.isFol])).2 (.inr hw'.1)
  have hI' := hI.back (hc := hc) hwu hwk hu he
  obtain ⟨hDw, hDu, hDo⟩ := interact_states (hc := hc) (C := C) hwu
  rw [hwk, hu, he] at hDu hDw
  simp only [δ] at hDu hDw
  have hWc := wsum_change (w := wR) hwu hDo
  rw [hwk, hu, hDu, hDw] at hWc
  simp only [wR] at hWc
  refine ⟨_, Protocol.reachable_of_ne hwu, ⟨hI',
    forall_of_change (P := fun q => q.isFi = false) hF hDo ?_ ?_,
    onePartial_of_change hO hDo ?_ ?_,
    forall_of_change (P := fun q => q.isLbar = false) hL hDo ?_ ?_⟩, .inr (by omega)⟩ <;>
    first | (rw [hDw]; rfl) | (rw [hDu]; rfl)

end Podc.NetworkConstructors.Cliques
