import Papers.PODC2014.RandomizationTwoHop.ViewGraph

-- CSLib candidate (paper-local for now; see README)

/-!
# Norris' theorem (Theorem 3) and Corollaries 1 and 2

Theorem 3 of the paper is cited from Norris (1995): in a labelled graph with `n` nodes, the view
`L_n(v)` determines `L_∞(v)`. We prove it by colour refinement: the partitions of the nodes by
their depth-`k` views get finer with `k`; once two consecutive partitions agree they agree forever
(`TEq` is defined by a uniform refinement step from tree depth `0`, i.e. from `L_1`), and a
strictly finer partition has more classes. With at most `n` classes the partition is stable from
tree depth `n - 1` on, i.e. from `L_n` on (`teq_stable`).

The same argument on the disjoint union gives a two-graph version (`teq_stable_two`): views of
nodes of graphs with `m` and `n` nodes that agree to tree depth `m + n - 1` agree forever. This is
used in the analysis of algorithm `A*` (Lemma 7).
-/

namespace Podc.RandomizationTwoHop

open SimpleGraph

variable {L : Type}

/-- Colour refinement stabilizes: a decreasing sequence of equivalence relations on a finite set
in which one stable step implies stability of the next one is constant from index `|X| - 1` on. -/
theorem refinement_stable {X : Type} [Finite X] (E : ℕ → X → X → Prop)
    (hequiv : ∀ k, Equivalence (E k)) (hanti : ∀ k x y, E (k + 1) x y → E k x y)
    (hstep : ∀ k, (∀ x y, E (k + 1) x y ↔ E k x y) → ∀ x y, E (k + 2) x y ↔ E (k + 1) x y) :
    ∀ x y, E (Nat.card X - 1) x y → ∀ k, E k x y := by
  intro x₀ y₀ hxy k
  have hne : Nonempty X := ⟨x₀⟩
  let S : ℕ → Setoid X := fun k => ⟨E k, hequiv k⟩
  let c : ℕ → ℕ := fun k => Nat.card (Quotient (S k))
  let φ : ∀ k, Quotient (S (k + 1)) → Quotient (S k) := fun k =>
    Quotient.map' id (fun a b h => hanti k a b h)
  have hφs : ∀ k, Function.Surjective (φ k) := by
    intro k q; induction q using Quotient.inductionOn with
    | h a => exact ⟨Quotient.mk _ a, rfl⟩
  have hc_le : ∀ k, c k ≤ c (k + 1) := fun k => Nat.card_le_card_of_surjective _ (hφs k)
  have hc_lt : ∀ k, ¬ (∀ x y, E (k + 1) x y ↔ E k x y) → c k < c (k + 1) := by
    intro k hk
    refine lt_of_le_of_ne (hc_le k) fun he => hk fun x y => ⟨hanti k x y, fun h => ?_⟩
    have hb := (hφs k).bijective_of_nat_card_le he.ge
    have : φ k (Quotient.mk _ x) = φ k (Quotient.mk _ y) := Quotient.sound h
    exact Quotient.exact (hb.1 this)
  have hc_card : ∀ k, c k ≤ Nat.card X := fun k =>
    Nat.card_le_card_of_surjective _ (Quotient.mk'_surjective (s := S k))
  have hc0 : 1 ≤ c 0 := by
    have : Nonempty (Quotient (S 0)) := ⟨Quotient.mk _ x₀⟩
    have : Finite (Quotient (S 0)) := Finite.of_surjective _ (Quotient.mk'_surjective (s := S 0))
    exact Nat.one_le_iff_ne_zero.2 (Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩)
  -- some index `s ≤ |X| - 1` is stable
  obtain ⟨s, hs, hstab⟩ : ∃ s ≤ Nat.card X - 1, ∀ x y, E (s + 1) x y ↔ E s x y := by
    by_contra hcon
    push Not at hcon
    have : ∀ j ≤ Nat.card X, c 0 + j ≤ c j := by
      intro j hj
      induction j with
      | zero => simp
      | succ j ih =>
        have := hc_lt j (by
          intro h; obtain ⟨x, y, hxy⟩ := hcon j (by omega)
          have := h x y; tauto)
        have := ih (by omega); omega
    have := this (Nat.card X) le_rfl
    have := hc_card (Nat.card X)
    omega
  -- from `s` on everything is constant
  have hconst : ∀ j, ∀ x y, E (s + j) x y ↔ E s x y := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hst : ∀ x y, E (s + j + 1) x y ↔ E (s + j) x y := by
        clear ih
        induction j with
        | zero => simpa using hstab
        | succ j ih' => exact hstep _ ih'
      intro x y; rw [← ih x y, ← hst x y, Nat.add_succ]
  rcases le_or_gt k (Nat.card X - 1) with hk | hk
  · -- antitone
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
    clear hconst hstab
    induction d generalizing k with
    | zero => simpa [hd] using hxy
    | succ d ih => exact hanti k _ _ (ih (k + 1) (by omega) (by omega))
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show s ≤ k by omega)
    obtain ⟨d', hd'⟩ := Nat.exists_eq_add_of_le hs
    exact (hconst d x₀ y₀).2 (by rw [← hconst d' x₀ y₀, ← hd']; exact hxy)

section
variable {V W : Type} (G : SimpleGraph V) (lG : V → L) (H : SimpleGraph W) (lH : W → L)

theorem teq_succ_succ_iff {k : ℕ}
    (h : ∀ x y, TEq G lG H lH (k + 1) x y ↔ TEq G lG H lH k x y) (x : V) (y : W) :
    TEq G lG H lH (k + 2) x y ↔ TEq G lG H lH (k + 1) x y := by
  show (lG x = lH y ∧ ∃ e : G.neighborSet x ≃ H.neighborSet y, ∀ w, TEq G lG H lH (k + 1) w.1 (e w).1) ↔
    (lG x = lH y ∧ ∃ e : G.neighborSet x ≃ H.neighborSet y, ∀ w, TEq G lG H lH k w.1 (e w).1)
  simp only [h]

/-- Colour refinement in one finite graph: views agreeing to tree depth `|V| - 1` (i.e.
`L_{|V|}`) agree to every depth. -/
theorem teq_stable [Finite V] {u v : V} (h : TEq G lG G lG (Nat.card V - 1) u v) (k : ℕ) :
    TEq G lG G lG k u v :=
  refinement_stable (fun k => TEq G lG G lG k)
    (fun k => ⟨TEq.refl k, TEq.symm, TEq.trans⟩) (fun _ _ _ h => h.of_succ)
    (fun _ hk x y => teq_succ_succ_iff G lG G lG hk x y) u v h k

/-- The embedding of a graph into a disjoint union is a local isomorphism. -/
theorem isLocalIso_inl : IsLocalIso G lG (G ⊕g H) (Sum.elim lG lH) Sum.inl where
  lab _ := rfl
  bij v := by
    refine ⟨fun x hx => by simpa using hx, Sum.inl_injective.injOn, fun y hy => ?_⟩
    rcases y with y | y
    · exact ⟨y, by simpa using hy, rfl⟩
    · simp at hy

theorem isLocalIso_inr : IsLocalIso H lH (G ⊕g H) (Sum.elim lG lH) Sum.inr where
  lab _ := rfl
  bij v := by
    refine ⟨fun x hx => by simpa using hx, Sum.inr_injective.injOn, fun y hy => ?_⟩
    rcases y with y | y
    · simp at hy
    · exact ⟨y, by simpa using hy, rfl⟩

/-- Colour refinement across two finite graphs with `m` and `n` nodes: views agreeing to tree
depth `m + n - 1` agree to every depth. -/
theorem teq_stable_two [Finite V] [Finite W] {u : V} {v : W}
    (h : TEq G lG H lH (Nat.card V + Nat.card W - 1) u v) (k : ℕ) : TEq G lG H lH k u v := by
  have hl := (isLocalIso_inl G lG H lH).teq
  have hr := (isLocalIso_inr G lG H lH).teq
  have h' : TEq (G ⊕g H) (Sum.elim lG lH) (G ⊕g H) (Sum.elim lG lH)
      (Nat.card (V ⊕ W) - 1) (Sum.inl u) (Sum.inr v) := by
    rw [Nat.card_sum]; exact ((hl _ u).symm.trans h).trans (hr _ v)
  exact ((hl k u).trans (teq_stable _ _ h' k)).trans (hr k v).symm

end

/-- **Theorem 3** (Norris). In a labelled graph with `n` nodes, `L_n(v)` determines `L_∞(v)`:
`L_n(u) = L_n(v)` implies `L_∞(u) = L_∞(v)`. -/
theorem theorem_3 (X : LGraph L) (u v : X.V) (h : ViewEq X u X v (Nat.card X.V)) :
    ViewEqInf X u X v :=
  teq_stable X.G X.lab h

/-- **Corollary 1.** In an `n`-node prime 2-hop coloured graph, `u = v` iff `L_n(u) = L_n(v)`. -/
theorem corollary_1 (X : LGraph L) (hX : X.TwoHop) (hP : Prime X) (u v : X.V) :
    u = v ↔ ViewEq X u X v (Nat.card X.V) := by
  constructor
  · rintro rfl; exact TEq.refl _ _
  · intro h; exact (lemma_4 X hX hP u v).2 (theorem_3 X u v h)

/-- **Corollary 2** (in the form used by the paper). For a 2-hop coloured graph `X` with
`n = |V∞|` different infinite views, the depth-`n` views separate exactly the classes of equal
infinite views. Hence the depth-`n` truncation is a bijection from `V∞` onto the node set `V*` of
the finite view graph, which is therefore isomorphic to `X∞` (`G* ≅ G∞`). -/
theorem corollary_2 (X : LGraph L) (hX : X.TwoHop) (u v : X.V) :
    ViewEq X u X v (Nat.card (viewLGraph X).V) ↔ ViewEqInf X u X v := by
  refine ⟨fun h k => ?_, fun h => h _⟩
  have hf := (lemma_2 X hX).toIsLocalIso.teq
  have h' := teq_stable (viewLGraph X).G (viewLGraph X).lab
    (((hf _ u).symm.trans h).trans (hf _ v)) k
  exact ((hf k u).trans h').trans (hf k v).symm

end Podc.RandomizationTwoHop
