import Papers.PODC2014.NetworkConstructors.CliquesInv

/-!
# Protocol 9 (`c`-Cliques): every rule preserves the invariant

One lemma per rule (`Inv.merge` for the four rules `(l_i, l_j, 0)`, `Inv.release`, `Inv.count`,
`Inv.connect`, `Inv.visit`, `Inv.cut`, `Inv.back`), and `inv_step`.
-/

namespace Podc.NetworkConstructors.Cliques

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem St

variable {c : ℕ} {hc : 3 ≤ c} {V : Type*} [Fintype V] [DecidableEq V]
  {C : Config V (St c)} {p : V → V} {ht : V → ℕ} {u v : V}

/-! ### Small helpers -/

omit [Fintype V] in
theorem card_filter_change {s : Finset V} {w₀ : V} {P Q : V → Bool} (hw₀ : w₀ ∈ s)
    (hPQ : ∀ w ∈ s, w ≠ w₀ → Q w = P w) :
    (s.filter fun w => Q w = true).card + (if P w₀ then 1 else 0) =
      (s.filter fun w => P w = true).card + (if Q w₀ then 1 else 0) := by
  have hc : (s.erase w₀).filter (fun w => Q w = true) = (s.erase w₀).filter (fun w => P w = true) :=
    Finset.filter_congr fun w hw => by
      rw [hPQ w (Finset.mem_of_mem_erase hw) (Finset.ne_of_mem_erase hw)]
  rw [← Finset.insert_erase hw₀, Finset.filter_insert, Finset.filter_insert, hc]
  have hn : w₀ ∉ (s.erase w₀).filter (fun w => P w = true) := by simp
  cases hQ : Q w₀ <;> cases hP : P w₀ <;> simp [Finset.card_insert_of_notMem hn]

omit [Fintype V] [DecidableEq V] in
theorem card_filter_congr {s : Finset V} {P Q : V → Bool} (hPQ : ∀ w ∈ s, Q w = P w) :
    (s.filter fun w => Q w = true).card = (s.filter fun w => P w = true).card := by
  rw [Finset.filter_congr fun w hw => by rw [hPQ w hw]]

theorem deg_eq_one {Q : Type*} {D : Config V Q} (huv : u ≠ v)
    (h : ∀ w, w ≠ v → (D.edge v w = true ↔ w = u)) : D.deg v = 1 := by
  unfold Config.deg
  rw [Finset.card_eq_one]
  refine ⟨u, ?_⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨hw, he⟩; exact (h w hw).1 he
  · intro hw; rw [hw]; exact ⟨huv, (h u huv).2 rfl⟩

namespace Inv

theorem p_eq (hI : Inv C p ht) {x : V} (h : (C.st x).isRoot = true) : p x = x :=
  (hI.root x).2 h

theorem p_ne (hI : Inv C p ht) {x : V} (h : (C.st x).isRoot = false) : p x ≠ x := fun h' => by
  rw [(hI.root x).1 h'] at h; exact Bool.noConfusion h

theorem kids_empty (hI : Inv C p ht) {x : V} (h : (C.st x).nkids = 0) : kids p x = ∅ :=
  Finset.card_eq_zero.1 (by rw [hI.nkids, h])

theorem not_mem_kids_of_empty (hI : Inv C p ht) {x w : V} (h : (C.st x).nkids = 0) :
    p w ≠ x ∨ w = x := by
  by_contra hc
  push Not at hc
  have : w ∈ kids p x := mem_kids.2 hc
  rw [hI.kids_empty h] at this
  simp at this

theorem parent_of_edge (hI : Inv C p ht) (huv : u ≠ v) (he : C.edge u v = true)
    (h : (C.st u).isFol = false) : p u = v ∨ p v = u :=
  (hI.edge u v huv (by simp [h])).1 he

/-- Edges at a non-numbered agent without children: only the edge to its parent. -/
theorem edge_of_leaf (hI : Inv C p ht) {x w : V} (hx : (C.st x).isFol = false)
    (hk : (C.st x).nkids = 0) (hw : w ≠ x) : C.edge x w = true ↔ p x = w := by
  rw [hI.edge x w (Ne.symm hw) (by simp [hx])]
  constructor
  · rintro (h | h)
    · exact h
    · rcases hI.not_mem_kids_of_empty (w := w) hk with h' | h'
      · exact absurd h h'
      · exact absurd h' hw
  · exact .inl

/-- The filter of the children by a predicate on the states after an interaction of `u` and `v`
equals the filter by the states before, if `u`, `v` are not children. -/
theorem card_filter_kids_interact (x : V) (hu : u ∉ kids p x) (hv : v ∉ kids p x)
    (P : St c → Bool) :
    ((kids p x).filter fun w => P (((cliques c hc).interact C u v).st w) = true).card =
      ((kids p x).filter fun w => P (C.st w) = true).card :=
  card_filter_congr fun w hw => by
    rw [Protocol.interact_st_other C (fun h => hu (by rw [← h]; exact hw))
      (fun h => hv (by rw [← h]; exact hw))]

theorem filter_kids_eq_zero (hI : Inv C p ht) (x : V) (hf : (C.st x).nfol = 0)
    (hvis : (C.st x).nvis = 0) :
    ((kids p x).filter fun w => (C.st w).isFol = true).card = 0 ∧
      ((kids p x).filter fun w => (C.st w).isVis = true).card = 0 :=
  ⟨by rw [hI.nfol, hf], by rw [hI.nvis, hvis]⟩

theorem not_fol_kids (hI : Inv C p ht) (x : V) (h : (C.st x).nfol = 0) :
    ∀ w ∈ kids p x, (C.st w).isFol = false := by
  intro w hw
  have h0 : ((kids p x).filter fun w => (C.st w).isFol = true).card = 0 := by rw [hI.nfol, h]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  simpa using h0 hw

theorem not_vis_kids (hI : Inv C p ht) (x : V) (h : (C.st x).nvis = 0) :
    ∀ w ∈ kids p x, (C.st w).isVis = false := by
  intro w hw
  have h0 : ((kids p x).filter fun w => (C.st w).isVis = true).card = 0 := by rw [hI.nvis, h]
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  simpa using h0 hw

end Inv

/-! ### The rules -/

theorem isVis_le_isFol (q : St c) (h : q.isVis = true) : q.isFol = true := by
  cases q <;> simp_all [isVis, isFol]

/-- The four rules `(l_i, l_j, 0) → …` (`v` joins the component of `u`). -/
theorem Inv.merge (hI : Inv C p ht) (huv : u ≠ v) {i hi j hj} (hu : C.st u = .l i hi)
    (hv : C.st v = .l j hj) {a' b' : St c}
    (hδ : δ c hc (C.st u) (C.st v) (C.edge u v) = (a', b', true))
    (ha_root : a'.isRoot = true) (hb_root : b'.isRoot = false) (ha_fol : a'.isFol = false)
    (ha_nk : a'.nkids = i + 1) (hb_nk : b'.nkids = j)
    (ha_nf : a'.nfol = if b'.isFol then 1 else 0) (ha_nv : a'.nvis = 0) (hb_nf : b'.nfol = 0)
    (hb_nv : b'.nvis = 0) (hb_vis : b'.isVis = false)
    (hb_fol : b'.isFol = true → b'.idx = 1 ∧ j = 0) :
    Inv ((cliques c hc).interact C u v) (Function.update p v u)
      (Function.update ht u (max (ht u) (ht v + 1))) := by
  have hpu : p u = u := hI.p_eq (by simp [hu, isRoot])
  have hpv : p v = v := hI.p_eq (by simp [hv, isRoot])
  have hkv : kids (Function.update p v u) v = kids p v := by
    ext w
    simp only [mem_kids]
    by_cases hw : w = v
    · simp [hw]
    · rw [Function.update_of_ne hw]
  have hku : kids (Function.update p v u) u = insert v (kids p u) := by
    ext w
    simp only [mem_kids, Finset.mem_insert]
    by_cases hw : w = v
    · subst hw; simp [hpv, Ne.symm huv]
    · rw [Function.update_of_ne hw]; simp [hw]
  have hvu : v ∉ kids p u := by simp [hpv, Ne.symm huv]
  have huu : u ∉ kids p u := by simp
  have huv' : u ∉ kids p v := by simp [hpu, huv]
  have hvv : v ∉ kids p v := by simp
  have hz := hI.filter_kids_eq_zero u (by simp [hu, St.nfol]) (by simp [hu, St.nvis])
  have hzv := hI.filter_kids_eq_zero v (by simp [hv, St.nfol]) (by simp [hv, St.nvis])
  have hDv : ((cliques c hc).interact C u v).st v = b' := by
    simp [Protocol.interact_st_right C huv, hδ]
  have hdisj : ∀ w ∈ kids p u, w ≠ v := fun w hw h => hvu (h ▸ hw)
  apply hI.interact huv hδ (fun x hx => Function.update_of_ne hx _ _)
    (.inr ⟨.inr hpv, .inl (by simp)⟩)
  · simp [Function.update_of_ne huv, hpu, ha_root]
  · simp [hb_root, huv]
  · intro x hx
    have hle : ∀ y, ht y ≤ Function.update ht u (max (ht u) (ht v + 1)) y := by
      intro y; by_cases hy : y = u
      · subst hy; simp
      · simp [hy]
    by_cases hxv : x = v
    · subst hxv; simp [Function.update_of_ne (Ne.symm huv)]
    · rw [Function.update_of_ne hxv] at hx ⊢
      have hxu : x ≠ u := fun h => hx (h ▸ hpu)
      rw [Function.update_of_ne hxu]
      exact lt_of_lt_of_le (hI.ht_lt x hx) (hle _)
  · simp [hu, isFol]
  · simp [hv, isFol]
  · intro _; simp
  · simp [ha_fol]
  · intro hb
    obtain ⟨h1, rfl⟩ := hb_fol hb
    rw [h1]
    refine deg_eq_one huv fun w hw => ?_
    by_cases hwu : w = u
    · subst hwu; simp [hδ]
    · rw [Protocol.interact_edge_other C (by tauto), hI.edge_of_leaf (by simp [hv, St.isFol])
        (by simp [hv, St.nkids]) hw, hpv]
      exact ⟨fun h => absurd h.symm hw, fun h => absurd h hwu⟩
  · exact fun h => absurd hpu h
  · exact fun h => absurd hpv h
  · rw [hku, Finset.card_insert_of_notMem hvu, hI.nkids u, hu, ha_nk]; rfl
  · rw [hkv, hI.nkids v, hv, hb_nk]; rfl
  · rw [hku, Finset.filter_insert, hDv, ha_nf]
    have h0 := card_filter_kids_interact (hc := hc) (C := C) u huu hvu St.isFol
    rw [hz.1] at h0
    split_ifs with hb
    · rw [Finset.card_insert_of_notMem (by simp [hvu]), h0]
    · exact h0
  · rw [hkv, card_filter_kids_interact v huv' hvv, hzv.1, hb_nf]
  · rw [hku, Finset.filter_insert, hDv, hb_vis]
    simp only [Bool.false_eq_true, ite_false]
    rw [card_filter_kids_interact u huu hvu, hz.2, ha_nv]
  · rw [hkv, card_filter_kids_interact v huv' hvv, hzv.2, hb_nv]

/-- Rule `(f_i, f, 1) → (f_{i−1}, l_0, 0)` (`f_1` becomes `f`): `v` is released. -/
theorem Inv.release (hI : Inv C p ht) (huv : u ≠ v) {i h1 h2} (hu : C.st u = .fi i h1 h2)
    (hv : C.st v = .f) (he : C.edge u v = true) :
    Inv ((cliques c hc).interact C u v) (Function.update p v v) ht := by
  have hδ : δ c hc (C.st u) (C.st v) (C.edge u v) =
      ((if h : 1 < i then St.fi (i - 1) (by omega) (by omega) else St.f),
        .l 0 (Nat.zero_le _), false) := by rw [hu, hv, he]; rfl
  have ha : ∀ a' : St c, a' = (if h : 1 < i then St.fi (i - 1) (by omega) (by omega) else St.f) →
      a'.isRoot = false ∧ a'.isFol = false ∧ a'.isVis = false ∧ a'.nkids = i - 1 ∧
        a'.nfol = 0 ∧ a'.nvis = 0 := by
    intro a' ha'
    subst ha'
    split_ifs with h
    · simp [St.isRoot, St.isFol, St.isVis, St.nkids, St.nfol, St.nvis]
    · simp [St.isRoot, St.isFol, St.isVis, St.nkids, St.nfol, St.nvis]; omega
  obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6⟩ := ha _ rfl
  have hvk : (C.st v).nkids = 0 := by simp [hv, St.nkids]
  have hpvu : p v = u := by
    rcases hI.parent_of_edge huv he (by simp [hu, St.isFol]) with h | h
    · rcases hI.not_mem_kids_of_empty (w := u) hvk with h' | h'
      · exact absurd h h'
      · exact absurd h' huv
    · exact h
  have hpu : p u ≠ u := hI.p_ne (by simp [hu, St.isRoot])
  have hpuv : p u ≠ v := by
    rcases hI.not_mem_kids_of_empty (w := u) hvk with h' | h'
    · exact h'
    · exact absurd h' huv
  have hvu : v ∈ kids p u := by simp [hpvu, Ne.symm huv]
  have hku : kids (Function.update p v v) u = (kids p u).erase v := by
    ext w
    simp only [mem_kids, Finset.mem_erase]
    by_cases hw : w = v
    · simp [hw]
    · rw [Function.update_of_ne hw]; simp [hw]
  have hkv : kids (Function.update p v v) v = ∅ := by
    rw [← hI.kids_empty hvk]
    ext w
    simp only [mem_kids]
    by_cases hw : w = v
    · simp [hw]
    · rw [Function.update_of_ne hw]
  apply hI.interact huv hδ (fun x hx => Function.update_of_ne hx _ _)
    (.inr ⟨.inl hpvu, .inr (by simp)⟩)
  · rw [Function.update_of_ne huv, ha1]; simp [hpu]
  · simp [St.isRoot]
  · intro x hx
    by_cases hxv : x = v
    · subst hxv; simp at hx
    · rw [Function.update_of_ne hxv] at hx ⊢; exact hI.ht_lt x hx
  · simp [hu, St.isFol]
  · simp [hv, St.isFol]
  · intro _
    rw [Function.update_of_ne huv, Function.update_self]
    simp [hpuv, Ne.symm huv]
  · simp [ha2]
  · simp [St.isFol]
  · intro _ _; rw [hu, ha2, ha3]; simp [St.isFol, St.isVis]
  · intro _ h; exact absurd hpvu h
  · rw [hku, Finset.card_erase_of_mem hvu, hI.nkids, hu, ha4]; rfl
  · rw [hkv]; rfl
  · rw [hku, ha5, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw
    have hw' := Finset.mem_erase.1 hw
    rw [Protocol.interact_st_other C (mem_kids.1 hw'.2).2 hw'.1,
      hI.not_fol_kids u (by simp [hu, St.nfol]) w hw'.2]
    simp
  · rw [hkv]; rfl
  · rw [hku, ha6, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro w hw
    have hw' := Finset.mem_erase.1 hw
    rw [Protocol.interact_st_other C (mem_kids.1 hw'.2).2 hw'.1,
      hI.not_vis_kids u (by simp [hu, St.nvis]) w hw'.2]
    simp
  · rw [hkv]; rfl

/-- Rule `(l̄_i, f, 1) → (l̄_{i+1}, 1, 1)` (`(l, 1, 1)` for `i = c − 2`). -/
theorem Inv.count (hI : Inv C p ht) (huv : u ≠ v) {i hi} (hu : C.st u = .lbar i hi)
    (hv : C.st v = .f) (he : C.edge u v = true) :
    Inv ((cliques c hc).interact C u v) p ht := by
  have hδ : δ c hc (C.st u) (C.st v) (C.edge u v) =
      ((if h : i < c - 2 then St.lbar (i + 1) (by omega) else St.lead),
        .num 1 le_rfl (by omega), true) := by rw [hu, hv, he]; rfl
  have ha : ∀ a' : St c, a' = (if h : i < c - 2 then St.lbar (i + 1) (by omega) else St.lead) →
      a'.isRoot = true ∧ a'.isFol = false ∧ a'.nkids = c - 1 ∧ a'.nfol = i + 1 ∧ a'.nvis = 0 := by
    intro a' ha'
    subst ha'
    split_ifs with h
    · simp [St.isRoot, St.isFol, St.nkids, St.nfol, St.nvis]
    · simp [St.isRoot, St.isFol, St.nkids, St.nfol, St.nvis]; omega
  obtain ⟨ha1, ha2, ha3, ha4, ha5⟩ := ha _ rfl
  have hvk : (C.st v).nkids = 0 := by simp [hv, St.nkids]
  have hpu : p u = u := hI.p_eq (by simp [hu, St.isRoot])
  have hpvu : p v = u := by
    rcases hI.parent_of_edge huv he (by simp [hu, St.isFol]) with h | h
    · exact absurd (hpu.symm.trans h) huv
    · exact h
  have hvu : v ∈ kids p u := by simp [hpvu, Ne.symm huv]
  have hDv : ((cliques c hc).interact C u v).st v = (δ c hc (C.st u) (C.st v) (C.edge u v)).2.1 :=
    by simp [Protocol.interact_st_right C huv]
  rw [hδ] at hDv
  apply hI.interact huv hδ (fun _ _ => rfl) (.inl rfl)
  · simp [hpu, ha1]
  · simp [hpvu, huv, St.isRoot]
  · exact hI.ht_lt
  · simp [hu, St.isFol]
  · simp [hv, St.isFol]
  · intro _; simp [hpvu]
  · simp [ha2]
  · intro _
    refine deg_eq_one huv fun w hw => ?_
    by_cases hwu : w = u
    · subst hwu; simp [hδ]
    · rw [Protocol.interact_edge_other C (by tauto), hI.edge_of_leaf (by simp [hv, St.isFol])
        hvk hw, hpvu]
      exact ⟨fun h => absurd h.symm hwu, fun h => absurd h hwu⟩
  · exact fun h => absurd hpu h
  · intro _ h; exact absurd hpvu h
  · rw [hI.nkids, hu, ha3]; rfl
  · rw [hI.kids_empty hvk]; rfl
  · have h := card_filter_change (s := kids p u) (P := fun w => (C.st w).isFol)
      (Q := fun w => (((cliques c hc).interact C u v).st w).isFol) hvu
      (fun w hw hwv => by rw [Protocol.interact_st_other C (mem_kids.1 hw).2 hwv])
    beta_reduce at h
    rw [hI.nfol u, hu, hDv, hv] at h
    rw [ha4]; simp [St.isFol, St.nfol] at h ⊢; omega
  · rw [hI.kids_empty hvk]; rfl
  · have h := card_filter_change (s := kids p u) (P := fun w => (C.st w).isVis)
      (Q := fun w => (((cliques c hc).interact C u v).st w).isVis) hvu
      (fun w hw hwv => by rw [Protocol.interact_st_other C (mem_kids.1 hw).2 hwv])
    beta_reduce at h
    rw [hI.nvis u, hu, hDv, hv] at h
    rw [ha5]; simp [St.isVis, St.nvis] at h ⊢; omega
  · rw [hI.kids_empty hvk]; rfl

/-- Rule `(i, j, 0) → (i + 1, j + 1, 1)` for `i, j < c − 1`. -/
theorem Inv.connect (hI : Inv C p ht) (huv : u ≠ v) {i h1 h2 j h3 h4}
    (hu : C.st u = .num i h1 h2) (hv : C.st v = .num j h3 h4) (hi : i < c - 1) (hj : j < c - 1)
    (he : C.edge u v = false) :
    Inv ((cliques c hc).interact C u v) p ht := by
  have hδ : δ c hc (C.st u) (C.st v) (C.edge u v) =
      (.num (i + 1) (by omega) (by omega), .num (j + 1) (by omega) (by omega), true) := by
    rw [hu, hv, he]; simp [δ, hi, hj]
  have huk : (C.st u).nkids = 0 := by simp [hu, St.nkids]
  have hvk : (C.st v).nkids = 0 := by simp [hv, St.nkids]
  apply hI.interact huv hδ (fun _ _ => rfl) (.inl rfl)
  · simp [hI.p_ne (x := u) (by simp [hu, St.isRoot]), St.isRoot]
  · simp [hI.p_ne (x := v) (by simp [hv, St.isRoot]), St.isRoot]
  · exact hI.ht_lt
  · simp [St.isFol]
  · simp [St.isFol]
  · simp [St.isFol]
  · intro _
    rw [Protocol.deg_interact_activate_left huv he (by simp [hδ]), hI.deg u (by simp [hu, St.isFol]),
      hu]; rfl
  · intro _
    rw [Protocol.deg_interact_activate_right huv he (by simp [hδ]),
      hI.deg v (by simp [hv, St.isFol]), hv]; rfl
  · intro _ _; simp [hu, St.isFol, St.isVis]
  · intro _ _; simp [hv, St.isFol, St.isVis]
  · rw [hI.kids_empty huk]; rfl
  · rw [hI.kids_empty hvk]; rfl
  · rw [hI.kids_empty huk]; rfl
  · rw [hI.kids_empty hvk]; rfl
  · rw [hI.kids_empty huk]; rfl
  · rw [hI.kids_empty hvk]; rfl

/-- Rule `(l, i, 1) → (r, l'_i, 1)`: the leader visits a follower. -/
theorem Inv.visit (hI : Inv C p ht) (huv : u ≠ v) {i h1 h2} (hu : C.st u = .lead)
    (hv : C.st v = .num i h1 h2) (he : C.edge u v = true) :
    Inv ((cliques c hc).interact C u v) p ht := by
  have hδ : δ c hc (C.st u) (C.st v) (C.edge u v) = (.r, .lp i h1 h2, true) := by
    rw [hu, hv, he]; rfl
  have hvk : (C.st v).nkids = 0 := by simp [hv, St.nkids]
  have hpu : p u = u := hI.p_eq (by simp [hu, St.isRoot])
  have hpvu : p v = u := by
    rcases hI.parent_of_edge huv he (by simp [hu, St.isFol]) with h | h
    · exact absurd (hpu.symm.trans h) huv
    · exact h
  have hvu : v ∈ kids p u := by simp [hpvu, Ne.symm huv]
  have hDv : ((cliques c hc).interact C u v).st v = (δ c hc (C.st u) (C.st v) (C.edge u v)).2.1 :=
    by simp [Protocol.interact_st_right C huv]
  rw [hδ] at hDv
  apply hI.interact huv hδ (fun _ _ => rfl) (.inl rfl)
  · simp [hpu, St.isRoot]
  · simp [hpvu, huv, St.isRoot]
  · exact hI.ht_lt
  · simp [hu, St.isFol]
  · simp [St.isFol]
  · intro _; simp [hpvu]
  · simp [St.isFol]
  · intro _
    rw [Protocol.deg_interact_of_edge_eq (by simp only [cliques_δ]; rw [hδ, he]), hI.deg v (by simp [hv, St.isFol]),
      hv]; rfl
  · exact fun h => absurd hpu h
  · intro _ h; exact absurd hpvu h
  · rw [hI.nkids, hu]; rfl
  · rw [hI.kids_empty hvk]; rfl
  · have h := card_filter_change (s := kids p u) (P := fun w => (C.st w).isFol)
      (Q := fun w => (((cliques c hc).interact C u v).st w).isFol) hvu
      (fun w hw hwv => by rw [Protocol.interact_st_other C (mem_kids.1 hw).2 hwv])
    beta_reduce at h
    rw [hI.nfol u, hu, hDv, hv] at h
    simp [St.isFol, St.nfol] at h ⊢; omega
  · rw [hI.kids_empty hvk]; rfl
  · have h := card_filter_change (s := kids p u) (P := fun w => (C.st w).isVis)
      (Q := fun w => (((cliques c hc).interact C u v).st w).isVis) hvu
      (fun w hw hwv => by rw [Protocol.interact_st_other C (mem_kids.1 hw).2 hwv])
    beta_reduce at h
    rw [hI.nvis u, hu, hDv, hv] at h
    simp [St.isVis, St.nvis] at h ⊢; omega
  · rw [hI.kids_empty hvk]; rfl

/-- Rule `(l'_i, l'_j, 1) → (l'_{i−1}, l'_{j−1}, 0)`: a wrong edge is removed. -/
theorem Inv.cut (hI : Inv C p ht) (huv : u ≠ v) {i h1 h2 j h3 h4}
    (hu : C.st u = .lp i h1 h2) (hv : C.st v = .lp j h3 h4) (hi : 2 ≤ i) (hj : 2 ≤ j)
    (he : C.edge u v = true) :
    Inv ((cliques c hc).interact C u v) p ht := by
  have hδ : δ c hc (C.st u) (C.st v) (C.edge u v) =
      (.lp (i - 1) (by omega) (by omega), .lp (j - 1) (by omega) (by omega), false) := by
    rw [hu, hv, he]; simp [δ, hi, hj]
  have huk : (C.st u).nkids = 0 := by simp [hu, St.nkids]
  have hvk : (C.st v).nkids = 0 := by simp [hv, St.nkids]
  apply hI.interact huv hδ (fun _ _ => rfl) (.inl rfl)
  · simp [hI.p_ne (x := u) (by simp [hu, St.isRoot]), St.isRoot]
  · simp [hI.p_ne (x := v) (by simp [hv, St.isRoot]), St.isRoot]
  · exact hI.ht_lt
  · simp [St.isFol]
  · simp [St.isFol]
  · simp [St.isFol]
  · intro _
    have := Protocol.deg_interact_deactivate_left (P := cliques c hc) huv he (by simp [hδ])
    rw [hI.deg u (by simp [hu, St.isFol]), hu] at this
    simp only [St.idx] at this ⊢; omega
  · intro _
    have := Protocol.deg_interact_deactivate_right (P := cliques c hc) huv he (by simp [hδ])
    rw [hI.deg v (by simp [hv, St.isFol]), hv] at this
    simp only [St.idx] at this ⊢; omega
  · intro _ _; simp [hu, St.isFol, St.isVis]
  · intro _ _; simp [hv, St.isFol, St.isVis]
  · rw [hI.kids_empty huk]; rfl
  · rw [hI.kids_empty hvk]; rfl
  · rw [hI.kids_empty huk]; rfl
  · rw [hI.kids_empty hvk]; rfl
  · rw [hI.kids_empty huk]; rfl
  · rw [hI.kids_empty hvk]; rfl

/-- Rule `(l'_i, r, 1) → (i, l, 1)`: the token returns to the leader. -/
theorem Inv.back (hI : Inv C p ht) (huv : u ≠ v) {i h1 h2} (hu : C.st u = .lp i h1 h2)
    (hv : C.st v = .r) (he : C.edge u v = true) :
    Inv ((cliques c hc).interact C u v) p ht := by
  have hδ : δ c hc (C.st u) (C.st v) (C.edge u v) = (.num i h1 h2, .lead, true) := by
    rw [hu, hv, he]; rfl
  have huk : (C.st u).nkids = 0 := by simp [hu, St.nkids]
  have hpv : p v = v := hI.p_eq (by simp [hv, St.isRoot])
  have hpuv : p u = v := by
    rcases hI.parent_of_edge (Ne.symm huv) ((C.symm u v).symm.trans he) (by simp [hv, St.isFol])
      with h | h
    · exact absurd (hpv.symm.trans h) (Ne.symm huv)
    · exact h
  have huv' : u ∈ kids p v := by simp [hpuv, huv]
  have hDu : ((cliques c hc).interact C u v).st u = (δ c hc (C.st u) (C.st v) (C.edge u v)).1 :=
    by simp
  rw [hδ] at hDu
  apply hI.interact huv hδ (fun _ _ => rfl) (.inl rfl)
  · simp [hpuv, Ne.symm huv, St.isRoot]
  · simp [hpv, St.isRoot]
  · exact hI.ht_lt
  · simp [St.isFol]
  · simp [hv, St.isFol]
  · intro _; simp [hpuv]
  · intro _
    rw [Protocol.deg_interact_of_edge_eq (by simp only [cliques_δ]; rw [hδ, he]), hI.deg u (by simp [hu, St.isFol]),
      hu]; rfl
  · simp [St.isFol]
  · intro _ h; exact absurd hpuv h
  · exact fun h => absurd hpv h
  · rw [hI.kids_empty huk]; rfl
  · rw [hI.nkids, hv]; rfl
  · rw [hI.kids_empty huk]; rfl
  · have h := card_filter_change (s := kids p v) (P := fun w => (C.st w).isFol)
      (Q := fun w => (((cliques c hc).interact C u v).st w).isFol) huv'
      (fun w hw hwu => by rw [Protocol.interact_st_other C hwu (mem_kids.1 hw).2])
    beta_reduce at h
    rw [hI.nfol v, hv, hDu, hu] at h
    simp [St.isFol, St.nfol] at h ⊢; omega
  · rw [hI.kids_empty huk]; rfl
  · have h := card_filter_change (s := kids p v) (P := fun w => (C.st w).isVis)
      (Q := fun w => (((cliques c hc).interact C u v).st w).isVis) huv'
      (fun w hw hwu => by rw [Protocol.interact_st_other C hwu (mem_kids.1 hw).2])
    beta_reduce at h
    rw [hI.nvis v, hv, hDu, hu] at h
    simp [St.isVis, St.nvis] at h ⊢; omega

/-- The invariant is preserved by every interaction. -/
theorem Inv.step (hI : Inv C p ht) (huv : u ≠ v) :
    ∃ p' ht', Inv ((cliques c hc).interact C u v) p' ht' := by
  rcases δ_cases hc (C.st u) (C.st v) (C.edge u v) with
    h | ⟨i, hi, j, hj, hu, hv, hji, he⟩ | ⟨i, h1, h2, hu, hv, he⟩ | ⟨i, hi, hu, hv, he⟩ |
    ⟨i, h1, h2, j, h3, h4, hu, hv, hi', hj', he⟩ | ⟨i, h1, h2, hu, hv, he⟩ |
    ⟨i, h1, h2, j, h3, h4, hu, hv, hi', hj', he⟩ | ⟨i, h1, h2, hu, hv, he⟩
  · exact ⟨p, ht, by rw [Protocol.interact_eq_self C h]; exact hI⟩
  · by_cases h : i < c - 2 <;> by_cases h0 : j = 0
    · subst h0
      exact ⟨_, _, hI.merge (hc := hc) huv hu hv (a' := .l (i + 1) (by omega)) (b' := .f)
        (by rw [hu, hv, he]; simp [δ, hji, h]) rfl rfl rfl rfl rfl (by simp [St.nfol, St.isFol])
        rfl rfl rfl rfl (by simp [St.isFol])⟩
    · exact ⟨_, _, hI.merge (hc := hc) huv hu hv (a' := .l (i + 1) (by omega))
        (b' := .fi j (by omega) (by omega))
        (by rw [hu, hv, he]; simp [δ, hji, h, h0]) rfl rfl rfl rfl rfl (by simp [St.nfol, St.isFol])
        rfl rfl rfl rfl (by simp [St.isFol])⟩
    · subst h0
      exact ⟨_, _, hI.merge (hc := hc) huv hu hv (a' := .lbar 1 (by omega))
        (b' := .num 1 le_rfl (by omega))
        (by rw [hu, hv, he]; simp [δ, hji, h]) rfl rfl rfl (by simp [St.nkids]; omega) rfl
        (by simp [St.nfol, St.isFol]) rfl rfl rfl rfl (fun _ => ⟨rfl, rfl⟩)⟩
    · exact ⟨_, _, hI.merge (hc := hc) huv hu hv (a' := .lbar 0 (by omega))
        (b' := .fi j (by omega) (by omega))
        (by rw [hu, hv, he]; simp [δ, hji, h, h0]) rfl rfl rfl (by simp [St.nkids]; omega) rfl
        (by simp [St.nfol, St.isFol]) rfl rfl rfl rfl (by simp [St.isFol])⟩
  · exact ⟨_, _, hI.release huv hu hv he⟩
  · exact ⟨_, _, hI.count huv hu hv he⟩
  · exact ⟨_, _, hI.connect huv hu hv hi' hj' he⟩
  · exact ⟨_, _, hI.visit huv hu hv he⟩
  · exact ⟨_, _, hI.cut huv hu hv hi' hj' he⟩
  · exact ⟨_, _, hI.back huv hu hv he⟩

/-- The initial configuration satisfies the invariant (every agent is a root `l_0`). -/
theorem inv_init : Inv ((cliques c hc).initConfig : Config V (St c)) id (fun _ => 0) := by
  have hk : ∀ u : V, kids id u = ∅ := fun u => by ext w; simp
  refine ⟨fun u => ?_, fun u h => absurd rfl h, fun u v huv _ => ?_, fun u h => ?_,
    fun u => ?_, fun u => ?_, fun u => ?_⟩
  · simp [Protocol.initConfig, St.isRoot]
  · simp [Protocol.initConfig, huv, Ne.symm huv]
  · simp [Protocol.initConfig, St.isFol] at h
  · simp [hk, Protocol.initConfig, St.nkids]
  · simp [hk, Protocol.initConfig, St.nfol]
  · simp [hk, Protocol.initConfig, St.nvis]

/-- Every reachable configuration satisfies the invariant for some forest. -/
theorem inv_reachable {C : Config V (St c)}
    (h : (cliques c hc).Reachable (cliques c hc).initConfig C) : ∃ p ht, Inv C p ht := by
  induction h with
  | refl => exact ⟨_, _, inv_init⟩
  | tail _ hst ih =>
    obtain ⟨p, ht, hI⟩ := ih
    obtain ⟨u, v, huv, rfl⟩ := hst
    exact hI.step huv

end Podc.NetworkConstructors.Cliques
