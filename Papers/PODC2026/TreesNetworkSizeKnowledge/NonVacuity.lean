import Papers.PODC2026.TreesNetworkSizeKnowledge.Theorem1

/-!
# Non-vacuity of Theorem 1

The hypotheses of `theorem1` are satisfiable: `fullAlg k` is a local algorithm (in the sense of
`Alg.IsLocal`) that solves `k`-hierarchical 2½-colouring on every tree. Each node waits until it
has seen the whole tree (eccentricity many rounds; the trivial `O(n)` upper bound mentioned in the
paper) and then outputs a fixed solution: level-`k` nodes are properly 2-coloured, all other nodes
decline.
-/

namespace Podc.TreesNetworkSizeKnowledge

open SimpleGraph

lemma levelSet_succ_subset (G : SimpleGraph ℕ) (V : Set ℕ) (i : ℕ) :
    levelSet G V (i + 1) ⊆ levelSet G V i := fun _ h => h.1

lemma levelSet_anti (G : SimpleGraph ℕ) (V : Set ℕ) {i i' : ℕ} (h : i ≤ i') :
    levelSet G V i' ⊆ levelSet G V i := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (levelSet_succ_subset G V _).trans ih

lemma InLevel.eq {G : SimpleGraph ℕ} {V : Set ℕ} {i i' v : ℕ} (h : InLevel G V i v)
    (h' : InLevel G V i' v) : i = i' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact h.2.2 (levelSet_anti G V (by omega) h'.2.1)
  · exact h'.2.2 (levelSet_anti G V (by omega) h.2.1)

lemma InLevel.mem {G : SimpleGraph ℕ} {V : Set ℕ} {i v : ℕ} (h : InLevel G V i v) : v ∈ V :=
  levelSet_anti G V (Nat.zero_le _) h.2.1

lemma Inst.reachable {I : Inst} {v x : ℕ} (hv : v ∈ I.V) (hx : x ∈ I.V) : I.G.Reachable v x := by
  have h := I.isTree.connected.preconnected ⟨v, hv⟩ ⟨x, hx⟩
  exact h.map (Embedding.induce (I.V : Set ℕ)).toHom

/-- The trivial algorithm: wait until the whole tree is seen, then output a fixed solution. -/
noncomputable def fullAlg (k : ℕ) : Alg Label where
  time I v := I.V.sup fun u => I.G.dist v u
  out I v := by
    classical
    exact if h : InLevel I.G I.V k v then
      (if I.isTree.colorable_two.some ⟨v, h.mem⟩ = 0 then .B else .W) else .D

lemma edist_lt_of_ecc {I : Inst} {v t x : ℕ} (hv : v ∈ I.V) (hx : x ∈ I.V)
    (hecc : ∀ x ∈ I.V, I.G.dist v x ≤ t) : I.G.edist v x < (t + 1 : ℕ) := by
  rw [← (Inst.reachable hv hx).coe_dist_eq_edist]
  exact_mod_cast Nat.lt_succ_of_le (hecc x hx)

/-- Every node reachable from `v` in `J` is a node of `I`, if `v` sees all of `I`. -/
lemma walk_mem {I J : Inst} {v t : ℕ} (hv : v ∈ I.V)
    (hag : Cslib.Local.GAgree I.G J.G v (t + 1)) (hecc : ∀ x ∈ I.V, I.G.dist v x ≤ t) :
    ∀ {a x : ℕ} (_ : J.G.Walk a x), a ∈ I.V → x ∈ I.V := by
  intro a x w
  induction w with
  | nil => exact id
  | cons hadj _ ih =>
    intro ha
    apply ih
    have h := (hag (edist_lt_of_ecc hv ha hecc) _).2 hadj
    exact I.adj_mem h.symm

lemma walk_mem' {I J : Inst} {v t : ℕ} (hv : v ∈ I.V)
    (hag : Cslib.Local.GAgree I.G J.G v (t + 1)) (hecc : ∀ x ∈ I.V, I.G.dist v x ≤ t) :
    ∀ {a x : ℕ} (_ : I.G.Walk a x), a ∈ J.V → x ∈ J.V := by
  intro a x w
  induction w with
  | nil => exact id
  | cons hadj _ ih =>
    intro _
    apply ih
    have h := (hag (edist_lt_of_ecc hv (I.adj_mem hadj) hecc) _).1 hadj
    exact J.adj_mem h.symm

/-- A node that sees all of `I` within radius `t` cannot be in a different instance with the same
radius-`t` view. -/
lemma eq_of_view {I J : Inst} {v t : ℕ} (hvI : v ∈ I.V) (hvJ : v ∈ J.V)
    (hag : Cslib.Local.GAgree I.G J.G v (t + 1)) (hecc : ∀ x ∈ I.V, I.G.dist v x ≤ t) :
    I = J := by
  have hV : I.V = J.V := by
    ext x
    constructor
    · intro hx
      obtain ⟨w⟩ := Inst.reachable hvI hx
      exact walk_mem' hvI hag hecc w hvJ
    · intro hx
      obtain ⟨w⟩ := Inst.reachable hvJ hx
      exact walk_mem hvI hag hecc w hvI
  have hG : I.G = J.G := by
    ext a b
    by_cases ha : a ∈ I.V
    · exact hag (edist_lt_of_ecc hvI ha hecc) b
    · constructor
      · intro h; exact absurd (I.adj_mem h) ha
      · intro h; exact absurd (hV ▸ J.adj_mem h) ha
  cases I; cases J
  simp only at hV hG
  subst hV hG
  rfl

theorem fullAlg_isLocal (k : ℕ) : (fullAlg k).IsLocal := by
  intro I J v t hvI hvJ hag
  have key : ∀ {I J : Inst}, v ∈ I.V → v ∈ J.V → Cslib.Local.GAgree I.G J.G v (t + 1) →
      (fullAlg k).time I v ≤ t → I = J := by
    intro I J hvI hvJ hag h
    refine eq_of_view hvI hvJ hag fun x hx => ?_
    exact (Finset.le_sup (f := fun u => I.G.dist v u) hx).trans h
  by_cases h : (fullAlg k).time I v ≤ t
  · obtain rfl := key hvI hvJ hag h
    exact ⟨Iff.rfl, fun _ => rfl⟩
  · refine ⟨⟨fun h' => absurd h' h, fun h' => ?_⟩, fun h' => absurd h' h⟩
    obtain rfl := key hvJ hvI hag.symm h'
    exact absurd h' h

theorem fullAlg_correct (k : ℕ) (I : Inst) : IsHierColoring k I ((fullAlg k).out I) := by
  classical
  have hout : ∀ v, (fullAlg k).out I v = if h : InLevel I.G I.V k v then
      (if I.isTree.colorable_two.some ⟨v, h.mem⟩ = 0 then Label.B else Label.W) else Label.D := by
    intro v; simp only [fullAlg]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hout, dite_eq_right (fun h => h.2.2 hv)]
  · intro v hv
    rw [hout, dite_eq_left hv]; split_ifs <;> simp
  · intro v _
    rw [hout]; split_ifs <;> simp
  · intro i hik v u hv hu hadj hcol
    by_cases hk : InLevel I.G I.V k v
    · have hik' : i = k := hv.eq hk
      subst hik'
      have hc := (I.isTree.colorable_two.some).valid (v := ⟨v, hv.mem⟩) (w := ⟨u, hu.mem⟩)
        (by simpa using hadj)
      rw [hout, hout, dite_eq_left hu, dite_eq_left hv]
      split_ifs with h1 h2 h2 <;> simp_all; omega
    · rw [hout, dite_eq_right hk] at hcol; simp at hcol
  · intro i _ v _ hE
    rw [hout] at hE; split_ifs at hE

/-- The hypotheses of `theorem1` are satisfiable. -/
theorem theorem1_hyps_satisfiable (k : ℕ) :
    ∃ A : Alg Label, A.IsLocal ∧ ∀ I : Inst, IsHierColoring k I (A.out I) :=
  ⟨fullAlg k, fullAlg_isLocal k, fullAlg_correct k⟩

end Podc.TreesNetworkSizeKnowledge
