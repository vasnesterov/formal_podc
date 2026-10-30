import Papers.PODC2026.ContentObliviousEulerian.Merging

/-!
# Merging a mutually pointing pair twice splits the circuit again

Frei, Gelles, Ghazy, Nolin, PODC 2026, §2.2, proof sketch of Lemma 5: "every circuit `C` selects
one neighboring circuit `C'` and merges into it", the merge being done by "a unique designated node
in `C` that borders the maximal `C'` … by locally chaining its port pairing".

With only two circuits `C₁, C₂` they select each other. If both merges are executed (each by the
node designated by its circuit, re-pairing as in Lemma 4), the second re-pairing acts on two pairs
that by then lie on the *same* circuit, and it can split that circuit again.

Example: `K_{2,4}` with `x = 0, y = 1` adjacent to `2, 3, 4, 5`. The pairing that pairs `2 ↔ 3`,
`4 ↔ 5` at `x` and `y` (and `x ↔ y` elsewhere) induces `C₁ = x 2 y 3 x` and `C₂ = x 4 y 5 x`.
Merging at `x` gives one circuit (`merge_at_x`); re-pairing at `y` the pair of `C₁` with the pair of
`C₂` (the merge requested by the other circuit) yields again two circuits,
`x 2 y 5 x` and `x 3 y 4 x` (`double_merge_splits`).

This is why our phase (`PhaseStep`) lets the larger circuit of a mutually pointing pair not merge.
-/

namespace Podc.ContentObliviousEulerian.DoubleMerge

open Finset SimpleGraph

/-- `K_{2,4}`: nodes `0, 1` are adjacent to `2, 3, 4, 5`. -/
def K24 : SimpleGraph (Fin 6) where
  Adj u w := (u.val < 2 ∧ 2 ≤ w.val) ∨ (2 ≤ u.val ∧ w.val < 2)
  symm := ⟨fun u w h => by omega⟩
  loopless := ⟨fun u h => by omega⟩

instance : DecidableRel K24.Adj := fun u w =>
  inferInstanceAs (Decidable ((u.val < 2 ∧ 2 ≤ w.val) ∨ (2 ≤ u.val ∧ w.val < 2)))

/-- The port pairing: `w ↔ w xor 1` at every node. -/
def flip (w : Fin 6) : Fin 6 := ![1, 0, 3, 2, 5, 4] w

lemma adj_flip : ∀ u w : Fin 6, K24.Adj u w → K24.Adj u (flip w) := by decide

/-- The initial pairing: `2 ↔ 3`, `4 ↔ 5` at `0` and `1`; `0 ↔ 1` at `2, 3, 4, 5`. -/
def π₀ : Pairing K24 where
  pair d := ⟨(d.fst, flip d.snd), adj_flip _ _ d.adj⟩
  pair_pair d := by
    apply Dart.ext; apply Prod.ext
    · rfl
    · show flip (flip d.snd) = d.snd; revert d; decide
  pair_ne d h := by
    have := congrArg (fun d : K24.Dart => d.snd) h
    revert this; simp only; generalize d.snd = w; revert w; decide
  fst_pair d := rfl

/-- The dart `(u, w)`. -/
def dt (u w : Fin 6) (h : K24.Adj u w := by decide) : K24.Dart := ⟨(u, w), h⟩

/-- The re-pairing of Lemma 4 with two pairs, explicitly. -/
lemma repair2_pair {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (π : Pairing G) {a a' : G.Dart} {v : V} (hv : ∀ i, (![a, a'] i).fst = v)
    (hinj : Function.Injective ![a, a']) (hab : ∀ i j, ![a, a'] i ≠ π.pair (![a, a'] j))
    (d : G.Dart) :
    (π.repair ![a, a'] hv hinj hab).pair d =
      if d = π.pair a then a' else if d = π.pair a' then a else if d = a then π.pair a'
      else if d = a' then π.pair a else π.pair d := by
  by_cases h1 : d = π.pair a
  · subst h1; rw [ite_eq_left rfl]; exact π.repair_pair_b hv hinj hab 0
  rw [ite_eq_right h1]
  by_cases h2 : d = π.pair a'
  · subst h2; rw [ite_eq_left rfl]; exact π.repair_pair_b hv hinj hab 1
  rw [ite_eq_right h2]
  by_cases h3 : d = a
  · subst h3; rw [ite_eq_left rfl]; exact π.repair_pair_a hv hinj hab 0
  rw [ite_eq_right h3]
  by_cases h4 : d = a'
  · subst h4; rw [ite_eq_left rfl]; exact π.repair_pair_a hv hinj hab 1
  rw [ite_eq_right h4]
  apply π.repair_pair_other hv hinj hab
  · intro i; fin_cases i <;> simpa
  · intro i; fin_cases i <;> simpa

/-- The circuit `C₁ = x 2 y 3 x`, as a set of darts. -/
def S₁ : Finset K24.Dart :=
  univ.filter (fun d => d.edge ∈ ({s(0, 2), s(2, 1), s(1, 3), s(3, 0)} : Finset (Sym2 (Fin 6))))

lemma S₁_closed : (∀ x ∈ S₁, π₀.pair x ∈ S₁) ∧ ∀ x ∈ S₁, x.symm ∈ S₁ := by decide

/-- Initially `C₁ = x 2 y 3 x` and `C₂ = x 4 y 5 x` are different circuits. -/
lemma C₁_ne_C₂ : ¬ π₀.Circ (dt 0 2) (dt 0 4) := by
  intro h
  have := Pairing.Circ.closed π₀ (S := (S₁ : Set K24.Dart)) S₁_closed.1 S₁_closed.2
    (by decide) h
  revert this; decide

/-- The pairing after the merge at `x = 0` (requested by one of the two circuits). -/
noncomputable def π₁ : Pairing K24 := π₀.join (dt 0 2) (dt 0 4) (show (dt 0 2).fst = (dt 0 4).fst from rfl) C₁_ne_C₂

lemma π₁_pair (d : K24.Dart) : π₁.pair d =
    if d = π₀.pair (dt 0 2) then dt 0 4 else if d = π₀.pair (dt 0 4) then dt 0 2
    else if d = dt 0 2 then π₀.pair (dt 0 4) else if d = dt 0 4 then π₀.pair (dt 0 2)
    else π₀.pair d := by
  unfold π₁ Pairing.join; rw [repair2_pair]

/-- After the merge at `x`, the four ports of `y = 1` lie on one circuit (in fact the merge at `x`
produced a single Eulerian circuit, by Lemma 4). -/
lemma merge_at_x : π₁.Circ (dt 1 2) (dt 1 4) := by
  unfold π₁; rw [π₀.join_circ]
  refine Or.inr ⟨Or.inl ?_, Or.inr ?_⟩
  · have h : π₀.next (dt 0 2) = (dt 1 2).symm := by decide
    have := (Pairing.Circ.next π₀ (dt 0 2)).trans (Pairing.Circ.symm_dart π₀ _)
    rwa [h, Dart.symm_symm] at this
  · have h : π₀.next (dt 0 4) = (dt 1 4).symm := by decide
    have := (Pairing.Circ.next π₀ (dt 0 4)).trans (Pairing.Circ.symm_dart π₀ _)
    rwa [h, Dart.symm_symm] at this

lemma hinj₂ : Function.Injective ![dt 1 2, dt 1 4] := by decide

lemma hab₂ : ∀ i j, ![dt 1 2, dt 1 4] i ≠ π₁.pair (![dt 1 2, dt 1 4] j) := by
  simp only [π₁_pair]; decide

/-- The pairing after the second merge, at `y = 1` (requested by the other circuit), which
re-pairs a pair of `C₁` with a pair of `C₂` as in Lemma 4, although both now lie on one circuit. -/
noncomputable def π₂ : Pairing K24 :=
  π₁.repair ![dt 1 2, dt 1 4] (v := 1) (by decide) hinj₂ hab₂

/-- The circuit `x 2 y 5 x` of `π₂`, as a set of darts. -/
def S₂ : Finset K24.Dart :=
  univ.filter (fun d => d.edge ∈ ({s(0, 2), s(2, 1), s(1, 5), s(5, 0)} : Finset (Sym2 (Fin 6))))

lemma S₂_closed : (∀ x ∈ S₂, π₂.pair x ∈ S₂) ∧ ∀ x ∈ S₂, x.symm ∈ S₂ := by
  unfold π₂
  simp only [repair2_pair, π₁_pair]
  decide

/-- **The double merge splits the circuit.** After both circuits of the mutually pointing pair
`C₁, C₂` performed their merge, the pairing has (at least) two circuits again: the ports `(x, 2)`
and `(x, 3)` lie on different circuits (`x 2 y 5 x` and `x 3 y 4 x`). -/
theorem double_merge_splits : ¬ π₂.Circ (dt 0 2) (dt 0 3) := by
  intro h
  have := Pairing.Circ.closed π₂ (S := (S₂ : Set K24.Dart)) S₂_closed.1 S₂_closed.2
    (by decide) h
  revert this; decide

end Podc.ContentObliviousEulerian.DoubleMerge
