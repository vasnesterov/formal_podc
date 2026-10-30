import Papers.PODC2012.WeakModelsModalLogic.Lemma16

/-!
# The graph of Figure 9a of Hella et al.

A 3-regular connected graph on 16 nodes without a 1-factor: a centre `0` adjacent to the top
nodes `1`, `6`, `11` of three gadgets; gadget `g ∈ {0, 1, 2}` has nodes
`a = 1+5g, b = 2+5g, c = 3+5g, d = 4+5g, e = 5+5g` and edges
`ab, ac, bd, be, cd, ce, de`.

* `fig9a_regular`, `fig9a_connected`, `fig9a_no_perfectMatching`.

No perfect matching: a gadget has 5 (odd) nodes, so a perfect matching matches some gadget node
to a node outside the gadget; the only such edge is `a–centre`. This happens for every gadget,
so the centre would be matched to two different nodes.
-/

namespace Podc.WeakModelsModalLogic

open Function

/-- The edges of Figure 9a (each listed once). -/
def fig9aEdges : List (Fin 16 × Fin 16) :=
  [(0, 1), (0, 6), (0, 11),
   (1, 2), (1, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5),
   (6, 7), (6, 8), (7, 9), (7, 10), (8, 9), (8, 10), (9, 10),
   (11, 12), (11, 13), (12, 14), (12, 15), (13, 14), (13, 15), (14, 15)]

/-- The 3-regular graph of Figure 9a (after [14, Figure 5.10]) without a 1-factor. -/
def fig9a : SimpleGraph (Fin 16) where
  Adj u v := (u, v) ∈ fig9aEdges ∨ (v, u) ∈ fig9aEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel fig9a.Adj := fun u v =>
  inferInstanceAs (Decidable ((u, v) ∈ fig9aEdges ∨ (v, u) ∈ fig9aEdges))

theorem fig9a_regular : ∀ v, deg fig9a v = 3 := by
  intro v
  rw [deg_eq_card_filter]
  revert v
  decide

theorem fig9a_connected : fig9a.Connected := by
  have step : ∀ u v : Fin 16, fig9a.Adj u v → fig9a.Reachable 0 u → fig9a.Reachable 0 v :=
    fun _ _ h hu => hu.trans h.reachable
  have h0 : fig9a.Reachable 0 0 := SimpleGraph.Reachable.refl _
  have h1 := step 0 1 (by decide) h0
  have h2 := step 1 2 (by decide) h1
  have h3 := step 1 3 (by decide) h1
  have h4 := step 2 4 (by decide) h2
  have h5 := step 2 5 (by decide) h2
  have h6 := step 0 6 (by decide) h0
  have h7 := step 6 7 (by decide) h6
  have h8 := step 6 8 (by decide) h6
  have h9 := step 7 9 (by decide) h7
  have h10 := step 7 10 (by decide) h7
  have h11 := step 0 11 (by decide) h0
  have h12 := step 11 12 (by decide) h11
  have h13 := step 11 13 (by decide) h11
  have h14 := step 12 14 (by decide) h12
  have h15 := step 12 15 (by decide) h12
  have hall : ∀ v, fig9a.Reachable 0 v := by
    intro v
    fin_cases v <;> assumption
  exact SimpleGraph.Connected.mk (fun u v => (hall u).symm.trans (hall v))

-- CSLib candidate
/-- A fixed-point-free involution cannot map a finite set of odd size into itself. -/
theorem exists_mem_not_mem_of_odd_card {α : Type*} {m : α → α} (hm : Involutive m)
    (hfp : ∀ x, m x ≠ x) (S : Finset α) (hS : Odd S.card) : ∃ x ∈ S, m x ∉ S := by
  by_contra h
  push Not at h
  let m' : S → S := fun x => ⟨m x, h x x.2⟩
  have hm' : Involutive m' := fun x => Subtype.ext (hm x)
  obtain ⟨x, hx⟩ := Involutive.exists_fixed_of_odd_card hm' (by simpa using hS)
  exact hfp x (congrArg Subtype.val hx)

/-- The node set of gadget `g`. -/
def fig9aGadget (g : Fin 3) : Finset (Fin 16) :=
  Finset.univ.filter fun v => 1 + 5 * (g : ℕ) ≤ v ∧ (v : ℕ) ≤ 5 + 5 * (g : ℕ)

theorem fig9aGadget_card (g : Fin 3) : (fig9aGadget g).card = 5 := by
  revert g; decide

/-- The only edge leaving gadget `g` joins its top node to the centre. -/
theorem fig9aGadget_exit (g : Fin 3) : ∀ x ∈ fig9aGadget g, ∀ y, fig9a.Adj x y →
    y ∉ fig9aGadget g → (x : ℕ) = 1 + 5 * (g : ℕ) ∧ y = 0 := by
  revert g; decide

theorem fig9a_no_perfectMatching : ¬ ∃ M : fig9a.Subgraph, M.IsPerfectMatching := by
  rintro ⟨M, hM⟩
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hM
  choose m hm huniq using hM
  have hinv : Involutive m := fun v => (huniq _ _ (hm v).symm).symm
  have hfp : ∀ v, m v ≠ v := fun v h => by
    have := M.adj_sub (hm v)
    rw [h] at this
    exact fig9a.loopless.irrefl v this
  have key : ∀ g : Fin 3, m ⟨1 + 5 * (g : ℕ), by omega⟩ = 0 := by
    intro g
    obtain ⟨x, hx, hmx⟩ := exists_mem_not_mem_of_odd_card hinv hfp (fig9aGadget g)
      (by rw [fig9aGadget_card]; decide)
    obtain ⟨h1, h2⟩ := fig9aGadget_exit g x hx (m x) (M.adj_sub (hm x)) hmx
    have : x = ⟨1 + 5 * (g : ℕ), by omega⟩ := Fin.ext h1
    rw [← this, h2]
  have e0 := key 0
  have e1 := key 1
  have : (⟨1, by omega⟩ : Fin 16) = ⟨6, by omega⟩ := by
    rw [← hinv ⟨1, _⟩, ← hinv ⟨6, _⟩]
    exact congrArg m (e0.trans e1.symm)
  exact absurd (congrArg Fin.val this) (by norm_num)

end Podc.WeakModelsModalLogic
