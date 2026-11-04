import Papers.PODC2011.PartialReversalAcyclicity.Model

/-!
# Section 4: `NewPR` keeps the graph acyclic

Invariant 4.1, Invariant 4.2 and Theorem 4.3.

"Left" and "right" refer to the paper's embedding of `G'init` in the plane with all edges
directed from left to right; for two neighbours `u`, `v` it only matters which of them is to the
left, i.e. whether `init u v` (`u` left of `v`) or `init v u`. Theorem 4.3 does not need a global
embedding either: the cycle is shown to be a cycle of `G'init` or of its reverse.

All invariants follow from one inductive invariant (`EdgeInv`): for an edge `{u,v}` with `u` to
the left of `v`, writing `a = count[u]`, `b = count[v]`, either `a = b` and the edge points
right iff `a` is even, or `a = b + 1` with `a` even and the edge points right, or `b = a + 1`
with `a` even and the edge points left. Together with the consistency of the two direction
variables of an edge (the analogue of Invariant 3.1 for `NewPR`, which the paper uses
implicitly), this is preserved by every step; Invariants 4.1 and 4.2 are its consequences.
-/

noncomputable section
open Classical

namespace Podc.PartialReversalAcyclicity

variable {V : Type*} {N : Network V}

/-- Flipping the edges of a sink to a set of its neighbours preserves consistency. -/
theorem DirConsistent.flipAt {dir : V → V → Dir} (hc : DirConsistent N dir) {w : V}
    (hw : IsSink N dir w) {X : Set V} (hX : X ⊆ N.nbrs w) :
    DirConsistent N (flipAt dir w X) := by
  intro x y hxy
  have hne : x ≠ y := Network.ne_of_adj hxy
  simp only [flipAt_apply]
  by_cases h1 : x = w ∧ y ∈ X
  · obtain ⟨rfl, hy⟩ := h1
    simp [hy, hne.symm]
  · by_cases h2 : y = w ∧ x ∈ X
    · obtain ⟨rfl, hx⟩ := h2
      simp [hx, hne]
    · simp only [h1, h2, ite_false]
      exact hc x y hxy

namespace NewPR

/-- The inductive invariant behind Invariants 4.1 and 4.2, for an edge with `u` left of `v`. -/
def EdgeInv (t : NewPRState V) (u v : V) : Prop :=
  (t.count u = t.count v ∧ (Even (t.count u) ↔ t.dir u v = .out)) ∨
  (t.count u = t.count v + 1 ∧ Even (t.count u) ∧ t.dir u v = .out) ∨
  (t.count v = t.count u + 1 ∧ Even (t.count u) ∧ t.dir u v = .inc)

variable (N) in
/-- The full inductive invariant of `NewPR`. -/
def Inv (t : NewPRState V) : Prop :=
  DirConsistent N t.dir ∧ ∀ u v, N.init u v → EdgeInv t u v

theorem inv_init : Inv N (init N) := by
  refine ⟨initDir_consistent, fun u v huv => Or.inl ⟨rfl, ?_⟩⟩
  simp [init, Network.init_asymm huv]

theorem effect_dir (w : V) (t : NewPRState V) (x y : V) :
    (effect N w t).dir x y =
      if x = w ∧ y ∈ revSet N t w then .out
      else if y = w ∧ x ∈ revSet N t w then .inc else t.dir x y := rfl

theorem inv_effect {t : NewPRState V} (ht : Inv N t) {w : V} (hw : IsSink N t.dir w) :
    Inv N (effect N w t) := by
  obtain ⟨hc, he⟩ := ht
  refine ⟨hc.flipAt hw (revSet_subset t w), fun u v huv => ?_⟩
  have hne : u ≠ v := by rintro rfl; exact Network.init_irrefl u huv
  have hvu : ¬ N.init v u := Network.init_asymm huv
  have hadj : N.Adj u v := Or.inl huv
  have hadj' : N.Adj v u := Or.inr huv
  have hE := he u v huv
  unfold EdgeInv at hE ⊢
  have hcount : (effect N w t).count = Function.update t.count w (t.count w + 1) := rfl
  simp only [hcount, Function.update_apply]
  by_cases hwu : u = w
  · -- `u` (the left endpoint) takes the step
    subst hwu
    have hd : t.dir u v = .inc := hw v hadj
    have hd' : (effect N u t).dir u v = if Even (t.count u) then t.dir u v else .out := by
      rw [effect_dir]
      by_cases he : Even (t.count u) <;> simp [revSet, he, huv, hvu, hne.symm]
    simp only [hd', ite_true, hne.symm, ite_false, hd]
    rcases hE with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have : ¬ Even (t.count u) := by rw [h2, hd]; simp
      right; left
      refine ⟨by omega, ?_, by simp [this]⟩
      rw [Nat.even_add_one]; exact this
    · simp_all
    · left
      refine ⟨by omega, ?_⟩
      simp [h2, Nat.even_add_one]
  · by_cases hwv : v = w
    · -- `v` (the right endpoint) takes the step
      subst hwv
      have hd : t.dir u v = .out := (hc.out_iff hadj).mpr (hw u hadj')
      have hd' : (effect N v t).dir u v = if Even (t.count v) then .inc else t.dir u v := by
        rw [effect_dir]
        by_cases he : Even (t.count v) <;> simp [revSet, he, huv, hvu, hne]
      simp only [hd', hwu, ite_false, ite_true, hd]
      rcases hE with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · have : Even (t.count u) := by rw [h2, hd]
        right; right
        refine ⟨by omega, this, ?_⟩
        rw [← h1]; simp [this]
      · have : ¬ Even (t.count v) := by
          intro hv; rw [h1, Nat.even_add_one] at h2; exact h2 hv
        left
        refine ⟨by omega, ?_⟩
        simp [this, h2]
      · simp_all
    · have hd' : (effect N w t).dir u v = t.dir u v := by
        rw [effect_dir]; simp [hwu, hwv]
      simpa [hd', hwu, hwv] using hE

theorem inv_of_reachable {t : NewPRState V} (ht : Reachable N t) : Inv N t := by
  induction ht with
  | refl => exact inv_init
  | tail _ hstep ih =>
    obtain ⟨w, -, hw, rfl⟩ := hstep
    exact inv_effect ih hw

theorem consistent_of_reachable {t : NewPRState V} (ht : Reachable N t) :
    DirConsistent N t.dir := (inv_of_reachable ht).1

/-- Invariant 4.1 of [Radeva–Lynch]. In any reachable state, for neighbours `u`, `v` with `u`
to the left of `v` (`init u v`): (a) if both parities are even, the edge is directed from left
to right (`u → v`); (b) if both are odd, it is directed from right to left (`v → u`). -/
theorem inv_4_1 {t : NewPRState V} (ht : Reachable N t) {u v : V} (huv : N.init u v) :
    (Even (t.count u) → Even (t.count v) → arcs N t.dir u v) ∧
    (Odd (t.count u) → Odd (t.count v) → arcs N t.dir v u) := by
  obtain ⟨hc, he⟩ := inv_of_reachable ht
  have hadj : N.Adj u v := Or.inl huv
  have hadj' : N.Adj v u := Or.inr huv
  rcases he u v huv with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨fun hu _ => ⟨hadj, h2.mp hu⟩, fun hu _ => ⟨hadj', ?_⟩⟩
    have : t.dir u v = .inc := by
      rw [← Nat.not_even_iff_odd] at hu
      simpa using mt h2.mpr hu
    exact (hc u v hadj).mp this
  · refine ⟨fun _ _ => ⟨hadj, h3⟩, fun hu _ => ?_⟩
    exact absurd h2 (Nat.not_even_iff_odd.mpr hu)
  · refine ⟨fun _ hv => ?_, fun hu _ => ?_⟩
    · rw [h1, Nat.even_add_one] at hv; exact absurd h2 hv
    · exact absurd h2 (Nat.not_even_iff_odd.mpr hu)

/-- Invariant 4.2 of [Radeva–Lynch]. In any reachable state, for neighbours `u`, `v`:
(a) `count[v] ∈ {count[u] − 1, count[u], count[u] + 1}`;
(b) if `count[u]` is odd and `v` is to the right of `u`, then `count[v] = count[u]`;
(c) if `count[u]` is even and `v` is to the left of `u`, then `count[v] = count[u]`;
(d) if `count[u] > count[v]`, the edge is directed from `u` to `v`. -/
theorem inv_4_2 {t : NewPRState V} (ht : Reachable N t) {u v : V} (huv : N.Adj u v) :
    (t.count v + 1 = t.count u ∨ t.count v = t.count u ∨ t.count v = t.count u + 1) ∧
    (Odd (t.count u) → N.init u v → t.count v = t.count u) ∧
    (Even (t.count u) → N.init v u → t.count v = t.count u) ∧
    (t.count u > t.count v → arcs N t.dir u v) := by
  obtain ⟨hc, he⟩ := inv_of_reachable ht
  have hadj' : N.Adj v u := Network.adj_comm.mp huv
  rcases huv with h | h
  · have hn : ¬ N.init v u := Network.init_asymm h
    rcases he u v h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact ⟨by omega, fun _ _ => h1.symm, fun _ h' => absurd h' hn, fun h' => by omega⟩
    · refine ⟨by omega, fun ho _ => absurd h2 (Nat.not_even_iff_odd.mpr ho),
        fun _ h' => absurd h' hn, fun _ => ⟨Or.inl h, h3⟩⟩
    · refine ⟨by omega, fun ho _ => absurd h2 (Nat.not_even_iff_odd.mpr ho),
        fun _ h' => absurd h' hn, fun h' => by omega⟩
  · have hn : ¬ N.init u v := Network.init_asymm h
    rcases he v u h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · exact ⟨by omega, fun _ h' => absurd h' hn, fun _ _ => h1, fun h' => by omega⟩
    · refine ⟨by omega, fun _ h' => absurd h' hn, fun hu _ => ?_, fun h' => by omega⟩
      rw [h1, Nat.even_add_one] at h2; exact absurd hu h2
    · refine ⟨by omega, fun _ h' => absurd h' hn, fun hu _ => ?_, fun _ => ?_⟩
      · rw [h1, Nat.even_add_one] at hu; exact absurd h2 hu
      · exact ⟨Or.inr h, (hc v u (Or.inl h)).mp h3⟩

/-- Along an arc the step count does not increase (from Invariant 4.2 (d)). -/
theorem count_le_of_arcs {t : NewPRState V} (ht : Reachable N t) {x y : V}
    (h : arcs N t.dir x y) : t.count y ≤ t.count x := by
  by_contra hlt
  have h' := (inv_4_2 ht (Network.adj_comm.mp h.1)).2.2.2 (Nat.lt_of_not_le hlt)
  have := ((consistent_of_reachable ht).out_iff h.1).mp h.2
  exact absurd (this.symm.trans h'.2) (by simp)

/-- A path along which `f` does not increase and that ends at a value `≥ f a` stays at the level
`f a`. -/
private theorem transGen_level {r : V → V → Prop} {f : V → ℕ}
    (hf : ∀ x y, r x y → f y ≤ f x) {a b : V} (h : Relation.TransGen r a b) :
    f b ≤ f a ∧ (f a ≤ f b → Relation.TransGen (fun x y => r x y ∧ f x = f a ∧ f y = f a) a b) := by
  induction h with
  | single hab =>
    exact ⟨hf _ _ hab, fun h => .single ⟨hab, rfl, le_antisymm (hf _ _ hab) h⟩⟩
  | @tail c b _ hcb ih =>
    have hcb' := hf _ _ hcb
    refine ⟨hcb'.trans ih.1, fun hab => ?_⟩
    have hc : f c = f a := le_antisymm ih.1 (hab.trans hcb')
    exact .tail (ih.2 (hab.trans hcb')) ⟨hcb, hc, le_antisymm (hcb'.trans hc.le) (hc ▸ hab)⟩

/-- Theorem 4.3 of [Radeva–Lynch]: in any reachable state of `NewPR` the directed graph `G'` is
acyclic. -/
theorem thm_4_3 {t : NewPRState V} (ht : Reachable N t) : IsAcyclic (arcs N t.dir) := by
  intro u hu
  have hc := consistent_of_reachable ht
  -- all nodes on the cycle have the same step count `c = count[u]`
  have hlev := (transGen_level (f := t.count) (fun x y h => count_le_of_arcs ht h) hu).2 le_rfl
  rcases Nat.even_or_odd (t.count u) with hev | hodd
  · -- even: every arc of the cycle goes from left to right, a cycle in `G'init`
    refine N.acyclic u (Relation.TransGen.mono (p := N.init) (fun x y hh => ?_) u u hlev)
    obtain ⟨hxy, hx, hy⟩ := hh
    rcases hxy.1 with h | h
    · exact h
    · exfalso
      have := (inv_4_1 ht h).1 (hy ▸ hev) (hx ▸ hev)
      have h1 := (hc.out_iff hxy.1).mp hxy.2
      exact absurd (h1.symm.trans this.2) (by simp)
  · -- odd: every arc goes from right to left, a cycle in the reverse of `G'init`
    have : Relation.TransGen (fun x y => N.init y x) u u :=
      Relation.TransGen.mono (p := fun x y => N.init y x) (fun x y hh => by
      obtain ⟨hxy, hx, hy⟩ := hh
      rcases hxy.1 with h | h
      · exfalso
        have := (inv_4_1 ht h).2 (hx ▸ hodd) (hy ▸ hodd)
        have h1 := (hc.out_iff hxy.1).mp hxy.2
        exact absurd (h1.symm.trans this.2) (by simp)
      · exact h) u u hlev
    exact N.acyclic u this.swap

end NewPR

end Podc.PartialReversalAcyclicity

end
