import Papers.PODC2016.SpaceTimeVerification.Basic

/-!
# Proposition 4 and Theorem 5 (the crossing tool) fail for `t ≥ 2`

Proposition 4 claims: if a configuration satisfying `P` contains `r` directed edges `e_i` whose
`t`-neighbourhoods `N_t(e_i)` are pairwise disjoint, have `q` nodes each and are isomorphic
(state-preserving, heads to heads, tails to tails), and the label size is `< log r / q`, then for some
`i < j` every connected component of the edge crossing `C(e_i, e_j, G)` is accepted. Theorem 5
concludes that the label size of every `t`-PLS is `Ω(log r / q)` when some component of every
crossing violates `P`.

The proof says that every node of `N_t(e_i) ∪ N_t(e_j)` has "the same" `t`-neighbourhood in `G` and
in the crossing. For `t ≥ 2` this is false when `e_i` lies on a short cycle: a node of a triangle
sees, in two rounds, that its two neighbours are adjacent; after crossing two triangles they lie
on a 6-cycle.

Counterexample (`t = 2`, `q = 3`, every `r ≥ 2`): `G_r` = `r` disjoint triangles
`{(i,0), (i,1), (i,2)}`, `e_i = ((i,0), (i,1))`; `P` = "every node lies on a triangle", `F` = all
graphs. All hypotheses of Proposition 4 and Theorem 5 hold (`triangles_hyp`), and a crossing of
two triangles is a 6-cycle on which `P` fails. But a 2-round verifier with *empty* labels decides
`P` (`triScheme`: a node accepts iff two of its neighbours are adjacent; this is a function of its
radius-2 ball, so it is allowed in the model with identifiers whose output does not depend on the
identifiers, and in the ball model `BallIso`). So the label size is `0` for every `r`, not
`Ω(log r / 3)` (`theorem_5_false`), and for every `i ≠ j` the 6-cycle component of `C(e_i, e_j)` is
rejected under every labelling (`proposition_4_false`).

In an *anonymous* network (views = universal-cover trees) the triangle and the 6-cycle look the
same, and the crossing argument goes through; Theorem 7 (a path, whose edges lie on no cycle) is
proved directly in `LowerBound.lean`.
-/

namespace Podc.SpaceTimeVerification

open SimpleGraph

variable {V : Type*}

/-- Definition 3: the `t`-neighbourhood of the edge `(T, H)`: the nodes within distance `t` of one
of its endpoints. -/
def edgeNbhd (G : SimpleGraph V) (t : ℕ) (e : V × V) : Set V :=
  {w | G.edist w e.1 ≤ t ∨ G.edist w e.2 ≤ t}

/-- Definition 2: the edge crossing `C(e, e', G)` of directed edges `e = (T, H)`,
`e' = (T', H')`: the edges `TH` and `T'H'` are replaced by `TH'` and `T'H`. -/
def crossing (G : SimpleGraph V) (e e' : V × V) : SimpleGraph V where
  Adj a b := (G.Adj a b ∧ s(a, b) ≠ s(e.1, e.2) ∧ s(a, b) ≠ s(e'.1, e'.2)) ∨
    (a ≠ b ∧ (s(a, b) = s(e.1, e'.2) ∨ s(a, b) = s(e'.1, e.2)))
  symm := ⟨fun a b h => by
    rcases h with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, by rwa [Sym2.eq_swap], by rwa [Sym2.eq_swap]⟩
    · exact Or.inr ⟨h1.symm, by rw [Sym2.eq_swap]; exact h2⟩⟩
  loopless := ⟨fun a h => by
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact G.loopless.irrefl a h1
    · exact h1 rfl⟩

/-- The hypotheses of Proposition 4 / items 1–2 of Theorem 5 for the edges `e 0, …, e (r-1)` of `G`
(states are trivial, so the isomorphisms are automatically state-preserving): the edges exist,
their `t`-neighbourhoods are pairwise disjoint and have `q` nodes, and for every `i` there is an
isomorphism of the induced neighbourhoods `N_t(e_0) → N_t(e_i)` mapping tail to tail and head to
head. (We ask for isomorphisms between any two of them, which is equivalent.) -/
structure CrossingHyp (G : SimpleGraph V) (t r q : ℕ) (e : Fin r → V × V) : Prop where
  adj : ∀ i, G.Adj (e i).1 (e i).2
  disjoint : ∀ i j, i ≠ j → Disjoint (edgeNbhd G t (e i)) (edgeNbhd G t (e j))
  card : ∀ i, (edgeNbhd G t (e i)).ncard = q
  iso : ∀ i j, ∃ σ : V → V, Set.BijOn σ (edgeNbhd G t (e i)) (edgeNbhd G t (e j)) ∧
    (∀ a ∈ edgeNbhd G t (e i), ∀ b ∈ edgeNbhd G t (e i), (G.Adj a b ↔ G.Adj (σ a) (σ b))) ∧
    σ (e i).1 = (e j).1 ∧ σ (e i).2 = (e j).2

/-! ### The counterexample: disjoint triangles -/

/-- `r` disjoint triangles on `ℕ × Fin 3` restricted to the first `r` copies. -/
def triangles (r : ℕ) : SimpleGraph (Fin r × Fin 3) where
  Adj x y := x.1 = y.1 ∧ x.2 ≠ y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

/-- "Every node lies on a triangle." -/
def TriP : CProp Unit := fun _ G _ => ∀ v, ∃ a b, G.Adj v a ∧ G.Adj v b ∧ G.Adj a b

/-- The family of all configurations. -/
def AllF : CProp Unit := fun _ _ _ => True

/-- A 2-round PLS for `TriP` with empty labels: a node accepts iff two of its neighbours are
adjacent. -/
def triScheme : TPLS Unit (List Bool) AllF TriP 2 where
  prove _ _ _ := []
  verify G _ _ v := ∃ a b, G.Adj v a ∧ G.Adj v b ∧ G.Adj a b
  isLocal G I ℓ v G' I' ℓ' w h hv := by
    obtain ⟨φ, rfl, -, -, hadj, -⟩ := h
    obtain ⟨a, b, ha, hb, hab⟩ := hv
    have h0 : G.edist v v < (2 : ℕ) := by simp
    have h1 : G.edist v a < (2 : ℕ) := by
      rw [edist_eq_one_iff_adj.2 ha]; norm_num
    exact ⟨φ a, φ b, hadj v h0 a ha, hadj v h0 b hb, hadj a h1 b hab⟩
  complete _ _ _ hP v := hP v
  sound _ _ _ _ h := h

/-- The label size of `triScheme` is `0`. -/
lemma triScheme_cost : triScheme.CostLE List.length (fun _ => 0) := by
  intro V _ G I _ _ v
  simp [triScheme]

/-- The directed edges `e_i = ((i,0), (i,1))`. -/
def triEdge (r : ℕ) (i : Fin r) : (Fin r × Fin 3) × (Fin r × Fin 3) := ((i, 0), (i, 1))

lemma triangles_reachable {r : ℕ} {x y : Fin r × Fin 3} (h : (triangles r).Reachable x y) :
    x.1 = y.1 := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h _ ih => exact h.1.trans ih

lemma triangles_edgeNbhd {r : ℕ} (i : Fin r) :
    edgeNbhd (triangles r) 2 (triEdge r i) = {w | w.1 = i} := by
  ext w
  simp only [edgeNbhd, triEdge, Set.mem_ofPred_eq]
  constructor
  · rintro (h | h) <;>
    · have := triangles_reachable (edist_ne_top_iff_reachable.1 (ne_top_of_le_ne_top
        (by simp) h))
      simpa using this
  · intro h
    by_cases h0 : w.2 = 0
    · left; rw [show w = (i, 0) from Prod.ext h h0]; simp
    · left
      have : (triangles r).Adj w (i, 0) := ⟨h, h0⟩
      rw [edist_eq_one_iff_adj.2 this]; norm_num

lemma triangles_tri {r : ℕ} (v : Fin r × Fin 3) :
    ∃ a b, (triangles r).Adj v a ∧ (triangles r).Adj v b ∧ (triangles r).Adj a b := by
  refine ⟨(v.1, v.2 + 1), (v.1, v.2 + 2), ?_, ?_, ?_⟩ <;>
    refine ⟨rfl, ?_⟩ <;> revert v <;> simp only [Prod.forall] <;> intro _ a <;> fin_cases a <;>
    decide

/-- The disjoint triangles satisfy all hypotheses of Proposition 4 and Theorem 5 with `t = 2`,
`q = 3` and `r` edges. -/
theorem triangles_hyp (r : ℕ) : CrossingHyp (triangles r) 2 r 3 (triEdge r) where
  adj i := ⟨rfl, by simp [triEdge]⟩
  disjoint i j hij := by
    rw [triangles_edgeNbhd, triangles_edgeNbhd, Set.disjoint_left]
    intro w h1 h2; exact hij (h1.symm.trans h2)
  card i := by
    rw [triangles_edgeNbhd]
    have : {w : Fin r × Fin 3 | w.1 = i} = (fun a => (i, a)) '' Set.univ := by
      ext w; simp only [Set.mem_ofPred_eq, Set.image_univ, Set.mem_range]
      exact ⟨fun h => ⟨w.2, Prod.ext h.symm rfl⟩, fun ⟨a, ha⟩ => ha ▸ rfl⟩
    rw [this, Set.ncard_image_of_injective _ (fun a b h => (Prod.ext_iff.1 h).2), Set.ncard_univ]
    simp
  iso i j := by
    refine ⟨fun x => (j, x.2), ?_, ?_, rfl, rfl⟩
    · rw [triangles_edgeNbhd, triangles_edgeNbhd]
      refine ⟨fun x _ => rfl, fun x hx y hy h => Prod.ext (hx.trans hy.symm)
        (Prod.ext_iff.1 h).2, fun y hy => ⟨(i, y.2), rfl, Prod.ext hy.symm rfl⟩⟩
    · rw [triangles_edgeNbhd]
      intro a ha b hb
      simp only [triangles, Set.mem_ofPred_eq] at ha hb ⊢
      exact ⟨fun h => ⟨trivial, h.2⟩, fun h => ⟨ha.trans hb.symm, h.2⟩⟩

/-- The crossing of the triangles `i` and `j`. -/
abbrev triCross {r : ℕ} (i j : Fin r) : SimpleGraph (Fin r × Fin 3) :=
  crossing (triangles r) (triEdge r i) (triEdge r j)

/-- The nodes of the triangles `i` and `j`: a connected component of their crossing. -/
def triPair {r : ℕ} (i j : Fin r) : Set (Fin r × Fin 3) := {w | w.1 = i ∨ w.1 = j}

lemma triCross_adj {r : ℕ} (i j : Fin r) (x y : Fin r × Fin 3) :
    (triCross i j).Adj x y ↔
      (x.1 = y.1 ∧ x.2 ≠ y.2 ∧ ¬ ((x.1 = i ∨ x.1 = j) ∧
        ((x.2 = 0 ∧ y.2 = 1) ∨ (x.2 = 1 ∧ y.2 = 0)))) ∨
      (x = (i, 0) ∧ y = (j, 1)) ∨ (x = (j, 1) ∧ y = (i, 0)) ∨
      (x = (j, 0) ∧ y = (i, 1)) ∨ (x = (i, 1) ∧ y = (j, 0)) := by
  obtain ⟨xa, xb⟩ := x
  obtain ⟨ya, yb⟩ := y
  simp only [triCross, crossing, triangles, triEdge, Sym2.eq_iff, Prod.mk.injEq, ne_eq]
  fin_cases xb <;> fin_cases yb <;> simp <;> grind

lemma triPair_closed {r : ℕ} (i j : Fin r) (a : Fin r × Fin 3) (ha : a ∈ triPair i j)
    (b : Fin r × Fin 3) (hab : (triCross i j).Adj a b) : b ∈ triPair i j := by
  simp only [triPair, Set.mem_ofPred_eq] at ha ⊢
  rw [triCross_adj] at hab
  rcases hab with ⟨h, -⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp_all

/-- The crossing of two triangles, restricted to their nodes, is connected (a 6-cycle). -/
lemma triPair_connected {r : ℕ} {i j : Fin r} (hij : i ≠ j) :
    ((triCross i j).induce (triPair i j)).Connected := by
  have mem : ∀ k a, k = i ∨ k = j → ((k, a) : Fin r × Fin 3) ∈ triPair i j := fun k a h => h
  let x : Fin r → Fin 3 → triPair i j := fun k a =>
    if h : k = i ∨ k = j then ⟨(k, a), mem k a h⟩ else ⟨(i, 0), mem i 0 (Or.inl rfl)⟩
  have hx : ∀ k a (h : k = i ∨ k = j), x k a = ⟨(k, a), mem k a h⟩ := fun k a h => by
    simp [x, h]
  have adj : ∀ k a k' b (h : k = i ∨ k = j) (h' : k' = i ∨ k' = j),
      (triCross i j).Adj (k, a) (k', b) →
        ((triCross i j).induce (triPair i j)).Reachable (x k a) (x k' b) := by
    intro k a k' b h h' hadj
    rw [hx k a h, hx k' b h']
    exact Adj.reachable (by simpa using hadj)
  have hji : j ≠ i := Ne.symm hij
  have e1 := adj i 0 i 2 (Or.inl rfl) (Or.inl rfl) (by rw [triCross_adj]; simp)
  have e2 := adj i 2 i 1 (Or.inl rfl) (Or.inl rfl) (by rw [triCross_adj]; simp)
  have e3 := adj i 1 j 0 (Or.inl rfl) (Or.inr rfl) (by rw [triCross_adj]; simp)
  have e4 := adj j 0 j 2 (Or.inr rfl) (Or.inr rfl) (by rw [triCross_adj]; simp)
  have e5 := adj j 2 j 1 (Or.inr rfl) (Or.inr rfl) (by rw [triCross_adj]; simp)
  have hall : ∀ v : triPair i j, ((triCross i j).induce (triPair i j)).Reachable (x i 0) v := by
    rintro ⟨⟨k, a⟩, hk⟩
    have hv : (⟨(k, a), hk⟩ : triPair i j) = x k a := (hx k a hk).symm
    rw [hv]
    rcases hk with rfl | rfl <;> fin_cases a
    · rfl
    · exact (e1.trans e2)
    · exact e1
    · exact (e1.trans e2).trans e3
    · exact (((e1.trans e2).trans e3).trans e4).trans e5
    · exact ((e1.trans e2).trans e3).trans e4
  have : Nonempty (triPair i j) := ⟨x i 0⟩
  exact ⟨fun u v => (hall u).symm.trans (hall v)⟩

/-- In the crossing of the triangles `i ≠ j`, the node `(i, 1)` lies on no triangle. -/
lemma triCross_no_triangle {r : ℕ} {i j : Fin r} (hij : i ≠ j) :
    ¬ ∃ a b, (triCross i j).Adj (i, 1) a ∧ (triCross i j).Adj (i, 1) b ∧ (triCross i j).Adj a b := by
  have hn : ∀ a, (triCross i j).Adj (i, 1) a → a = (i, 2) ∨ a = (j, 0) := by
    rintro ⟨k, c⟩ h
    rw [triCross_adj] at h
    fin_cases c <;> simp_all
  rintro ⟨a, b, ha, hb, hab⟩
  rcases hn a ha with rfl | rfl <;> rcases hn b hb with rfl | rfl <;>
    rw [triCross_adj] at hab <;> simp_all [Ne.symm hij]

/-- **Theorem 5 is false** (for `t = 2`, in the model where a node sees its labelled radius-`t`
ball, e.g. with identifiers and identifier-independent outputs). For every `r ≥ 2`, the
configuration of `r` disjoint triangles satisfies `P` = "every node lies on a triangle" and all
hypotheses of Theorem 5 with `t = 2`, `q = 3` (items 1–3: `CrossingHyp`, and for `i ≠ j` the
crossing `C(e_i, e_j)` has a connected component, the 6-cycle `triPair i j`, violating `P`). Yet
`triScheme` is a 2-PLS for `P` with label size `0`; Theorem 5 claims label size
`Ω(log r / 3)`, unbounded in `r`. -/
theorem theorem_5_false (r : ℕ) :
    TriP _ (triangles r) (fun _ => ()) ∧ CrossingHyp (triangles r) 2 r 3 (triEdge r) ∧
      (∀ i j : Fin r, i ≠ j →
        (∀ a ∈ triPair i j, ∀ b, (triCross i j).Adj a b → b ∈ triPair i j) ∧
        ((triCross i j).induce (triPair i j)).Connected ∧
        ¬ TriP _ ((triCross i j).induce (triPair i j)) (fun _ => ())) ∧
      triScheme.CostLE List.length (fun _ => 0) := by
  refine ⟨triangles_tri, triangles_hyp r, fun i j hij => ⟨triPair_closed i j,
    triPair_connected hij, fun h => ?_⟩, triScheme_cost⟩
  obtain ⟨a, b, ha, hb, hab⟩ := h ⟨(i, 1), Or.inl rfl⟩
  exact triCross_no_triangle hij ⟨a.1, b.1, ha, hb, hab⟩

/-- **Proposition 4 is false** (for `t = 2`, same model): with `r ≥ 2` disjoint triangles and the
label size `0 < log₂ r / 3` of `triScheme`, Proposition 4 promises `i < j` such that every connected
component of `C(e_i, e_j, G)` is accepted; but for every `i ≠ j` and every labelling, a node of the
6-cycle component rejects. -/
theorem proposition_4_false {r : ℕ} {i j : Fin r} (hij : i ≠ j)
    (ℓ : triPair i j → List Bool) :
    ∃ v, ¬ triScheme.verify ((triCross i j).induce (triPair i j)) (fun _ => ()) ℓ v := by
  refine ⟨⟨(i, 1), Or.inl rfl⟩, fun ⟨a, b, ha, hb, hab⟩ => ?_⟩
  exact triCross_no_triangle hij ⟨a.1, b.1, ha, hb, hab⟩

end Podc.SpaceTimeVerification
