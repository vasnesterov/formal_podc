import Papers.PODC2020.BinaryLabelingClassification.Families

/-!
# Existence of solutions and the `O(n)` upper bounds of §8

Upper-bound halves of Theorems 8.1 and 8.3 of *Classification of Distributed Binary Labeling
Problems* (Balliu et al., arXiv:1911.13294v3).

* `whiteSolvable_card`: every problem that has a solution on every instance on `V` is solvable
  in `n = |V|` rounds (gather the whole tree, pick a solution canonically; *localization trick*).
* `va_exists`: problems of family V.a always have a solution (root the tree, label an edge by the
  parity of `⌊dist(r, u)/2⌋` of its white endpoint `u`).
* `viHard_exists`: the hardest problem of family VI.b (`W = 010⁺`, `B = 0⁺10`) always has a
  solution (root the tree at a leaf, put an edge into `X` iff its black endpoint is the parent of
  its white endpoint, i.e. orient the edges *away from* the leaf).
* `theorem_8_1_upper`, `theorem_8_3`: the `O(n)` upper bounds for V.a/V.b and VI.a/VI.b.

## Remark on the proof of Theorem 8.3

With the paper's convention (an edge in `X` is oriented from its black to its white endpoint),
`W = {1}`, `B = {δ − 1}` asks that every relevant node has indegree exactly `1`. Orienting all
edges *towards* a leaf root gives a non-root node of degree `k` indegree `k − 1`, which violates
the constraints for `k ≥ 3`; the correct choice is to orient *away from* the leaf root (every
non-root node then has indegree `1`, and the root is a leaf hence irrelevant). The same slip
appears in the remark about Theorem 8.2 ("orient a tree towards a root"). This is a harmless
convention error.
-/

namespace Podc.BinaryLabeling

open SimpleGraph Cslib.Local

variable {V : Type*}

/-! ### Tree facts -/

section Tree

variable {G : SimpleGraph V}

-- CSLib candidate
/-- In a tree, every node `v ≠ r` has a neighbour one step closer to `r` (its parent). -/
lemma IsTree.exists_adj_dist_add_one (hG : G.IsTree) {r v : V} (hv : v ≠ r) :
    ∃ p, G.Adj v p ∧ G.dist r p + 1 = G.dist r v := by
  obtain ⟨q, hq, hql⟩ := (hG.connected r v).exists_path_of_dist
  cases hrev : q.reverse with
  | nil => exact absurd rfl hv
  | cons h q' =>
    rename_i p
    refine ⟨p, h, ?_⟩
    have hlen : q'.length + 1 = G.dist r v := by
      have := congrArg Walk.length hrev
      simp only [Walk.length_reverse, Walk.length_cons] at this
      omega
    have hle : G.dist r p ≤ q'.length := by
      rw [dist_comm]; exact dist_le q'
    rcases hG.dist_eq_dist_add_one_of_adj r h with h1 | h1 <;> omega

-- CSLib candidate
/-- In a tree, a node has at most one neighbour one step closer to a given root. -/
lemma IsTree.eq_of_adj_dist_add_one (hG : G.IsTree) {r v p p' : V}
    (hp : G.Adj v p) (hd : G.dist r p + 1 = G.dist r v)
    (hp' : G.Adj v p') (hd' : G.dist r p' + 1 = G.dist r v) : p = p' := by
  obtain ⟨q, -, hql⟩ := (hG.connected r p).exists_path_of_dist
  obtain ⟨q', -, hql'⟩ := (hG.connected r p').exists_path_of_dist
  have h1 : (q.concat hp.symm).IsPath :=
    Walk.isPath_of_length_eq_dist _ (by simp [hql, hd])
  have h2 : (q'.concat hp'.symm).IsPath :=
    Walk.isPath_of_length_eq_dist _ (by simp [hql', hd'])
  have heq : q.concat hp.symm = q'.concat hp'.symm :=
    congrArg Subtype.val ((hG.isAcyclic.subsingleton_path _ _).elim ⟨_, h1⟩ ⟨_, h2⟩)
  have e1 : p = (q.concat hp.symm).penultimate :=
    hG.isAcyclic.eq_penultimate_of_adj_end h1 hp (by simp [Walk.support_concat])
  have e2 : p' = (q.concat hp.symm).penultimate :=
    hG.isAcyclic.eq_penultimate_of_adj_end h1 hp' (by rw [heq]; simp [Walk.support_concat])
  rw [e1, e2]

-- CSLib candidate
/-- In a tree, the neighbours of `v ≠ r` closer to `r` form a singleton (the parent). -/
lemma IsTree.parentSet_eq (hG : G.IsTree) {r v : V} (hv : v ≠ r) :
    ∃ p, G.Adj v p ∧ G.dist r p + 1 = G.dist r v ∧
      {w | G.Adj v w ∧ G.dist r w + 1 = G.dist r v} = {p} := by
  obtain ⟨p, hp, hd⟩ := IsTree.exists_adj_dist_add_one hG hv
  refine ⟨p, hp, hd, Set.ext fun w => ⟨fun ⟨hw, hdw⟩ => ?_, ?_⟩⟩
  · exact IsTree.eq_of_adj_dist_add_one hG hw hdw hp hd
  · rintro rfl; exact ⟨hp, hd⟩

-- CSLib candidate
/-- In a tree, the neighbours of `v` farther from `r` (the children) are all neighbours except
those closer to `r` (the parent). -/
lemma IsTree.childSet_eq (hG : G.IsTree) (r v : V) :
    {w | G.Adj v w ∧ G.dist r v + 1 = G.dist r w} =
      G.neighborSet v \ {w | G.Adj v w ∧ G.dist r w + 1 = G.dist r v} := by
  ext w
  simp only [Set.mem_ofPred_eq, Set.mem_sdiff, mem_neighborSet, not_and]
  constructor
  · rintro ⟨hw, hd⟩; exact ⟨hw, fun _ => by omega⟩
  · rintro ⟨hw, hd⟩
    rcases hG.dist_eq_dist_add_one_of_adj r hw with h | h
    · exact absurd h.symm (hd hw)
    · exact ⟨hw, h.symm⟩

/-- A connected graph on `n` nodes has diameter `< n`. -/
lemma Connected.edist_lt_card [Fintype V] (hG : G.Connected) (u v : V) :
    G.edist u v < Fintype.card V := by
  obtain ⟨p, hp, -⟩ := (hG u v).exists_path_of_dist
  exact (edist_le p).trans_lt (by exact_mod_cast hp.length_lt)

/-- A finite tree has a node of degree at most `1`. -/
lemma IsTree.exists_deg_le_one [Finite V] (hG : G.IsTree) : ∃ r, deg G r ≤ 1 := by
  classical
  have := Fintype.ofFinite V
  rcases subsingleton_or_nontrivial V with hV | hV
  · obtain ⟨r⟩ := hG.connected.nonempty
    refine ⟨r, ?_⟩
    simp [deg]
  · obtain ⟨r, hr⟩ := hG.exists_vert_degree_one_of_nontrivial
    exact ⟨r, by rw [deg, ncard_neighborSet, hr]⟩

end Tree

/-! ### Generic facts about solutions -/

/-- Solutions only depend on the labels of edges. -/
lemma IsSolution.congr {P : Problem} {G : SimpleGraph V} {f : V → Bool} {x y : V → V → Bool}
    (hx : IsSolution P G f x) (h : ∀ v w, G.Adj v w → y v w = x v w) : IsSolution P G f y := by
  have hdeg : ∀ v, degX G y v = degX G x v := by
    intro v
    unfold degX
    congr 1
    ext w
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h v w h1 ▸ h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, (h v w h1).symm ▸ h2⟩
  refine ⟨fun v w hvw => ?_, fun v hv hd => hdeg v ▸ hx.2.1 v hv hd,
    fun v hv hd => hdeg v ▸ hx.2.2 v hv hd⟩
  rw [h v w hvw, h w v hvw.symm]; exact hx.1 hvw

/-- The labelling in which the edge between a white node `u` and a black node `b` gets the label
`g u b`. -/
def pairLabel (f : V → Bool) (g : V → V → Bool) : V → V → Bool :=
  fun v w => if f v then g v w else g w v

lemma pairLabel_symm {G : SimpleGraph V} {f : V → Bool} (hf : IsProper G f) (g : V → V → Bool)
    {v w : V} (h : G.Adj v w) : pairLabel f g v w = pairLabel f g w v := by
  have := hf h
  unfold pairLabel
  cases hv : f v <;> cases hw : f w <;> simp_all

/-! ### Every solvable problem is solvable in `n` rounds -/

/-- The `n`-round algorithm of the localization trick: `u` picks a solution for its radius-`n`
view (if there is one) and outputs its row. -/
noncomputable def globalAlg (P : Problem) (n : ℕ) : Algorithm V :=
  fun G f u => Classical.epsilon (fun x => IsSolution P (loc G u n) (mask G u n f) x) u

lemma isLocal_globalAlg (P : Problem) (n : ℕ) : IsLocal n (globalAlg (V := V) P n) := by
  intro G f G' f' u hv
  simp only [globalAlg, hv.loc_eq, hv.mask_eq]

/-- Every problem that is solvable on all instances on `V` can be solved in `|V|` rounds (used in
the proofs of Theorems 8.1 and 8.3). -/
theorem whiteSolvable_card [Fintype V] (P : Problem)
    (h : ∀ (G : SimpleGraph V) (f : V → Bool), IsInstance G f → ∃ x, IsSolution P G f x) :
    WhiteSolvable P V (Fintype.card V) := by
  refine ⟨globalAlg P _, isLocal_globalAlg P _, fun G f hGf => ?_⟩
  have hlt := Connected.edist_lt_card hGf.1.connected
  have hloc : ∀ u, loc G u (Fintype.card V) = G := by
    intro u; ext x y
    simp only [loc, and_iff_left_iff_imp]
    exact fun _ => Or.inl (hlt u x)
  have hmask : ∀ u, mask G u (Fintype.card V) f = f := by
    intro u; funext w; exact mask_of_le (hlt u w).le
  set x := Classical.epsilon (fun x => IsSolution P G f x) with hxdef
  have hx : IsSolution P G f x := Classical.epsilon_spec (h G f hGf)
  have hA : ∀ u, globalAlg P (Fintype.card V) G f u = x u := by
    intro u; simp only [globalAlg, hloc, hmask, hxdef]
  refine hx.congr fun v w hvw => ?_
  simp only [whiteOut, hA]
  split_ifs
  · rfl
  · exact (hx.1 hvw).symm

/-! ### Family V.a always has a solution -/

/-- Problems of family V.a are solvable on every instance (proof of Theorem 8.1: orient the
edges from one colour class of the underlying tree to the other). Concretely: root the tree at a
node `r` of degree `≤ 1` and put the edge `{u, b}` (`u` white) into `X` iff `⌊dist(r, u)/2⌋` is
even. -/
theorem va_exists [Finite V] {P : Problem} (hP : P.IsVa) {G : SimpleGraph V} {f : V → Bool}
    (h : IsInstance G f) : ∃ x, IsSolution P G f x := by
  obtain ⟨hδ, hW, hB⟩ := hP
  obtain ⟨hG, hf⟩ := h
  obtain ⟨r, hr⟩ := IsTree.exists_deg_le_one hG
  let L : V → Bool := fun u => decide (G.dist r u / 2 % 2 = 0)
  refine ⟨pairLabel f (fun u _ => L u), fun v w hvw => pairLabel_symm hf _ hvw, ?_, ?_⟩
  · -- white nodes: all incident edges carry the same label
    intro u hu hdu
    rw [hW]
    cases hL : L u
    · left
      unfold degX
      convert Set.ncard_empty V
      ext w; simp [pairLabel, hu, hL]
    · right
      show degX G _ u = P.d
      rw [← hdu]
      unfold degX deg
      congr 1
      ext w; simp [pairLabel, hu, hL]
  · -- black nodes of degree 2: the parent and the child get different labels
    intro b hb hd
    rw [hB, hδ] at *
    have hbr : b ≠ r := by rintro rfl; omega
    obtain ⟨p, hp, hpd, hpar⟩ := IsTree.parentSet_eq hG (r := r) hbr
    have hch := IsTree.childSet_eq hG r b
    rw [hpar] at hch
    have hc1 : (G.neighborSet b \ {p}).ncard = 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem (show p ∈ G.neighborSet b from hp)]; unfold deg at hd; omega
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 hc1
    have hcm : c ∈ G.neighborSet b \ {p} := hc ▸ rfl
    have hcd : c ∈ {w | G.Adj b w ∧ G.dist r b + 1 = G.dist r w} := hch ▸ hcm
    have hcp : c ≠ p := hcm.2
    have hN : G.neighborSet b = {p, c} := by
      rw [← Set.insert_sdiff_self_of_mem (show p ∈ G.neighborSet b from hp), hc]
    have hLpc : L c = !L p := by
      simp only [L]
      have := hcd.2
      have e : G.dist r c = G.dist r p + 2 := by omega
      rw [e]
      by_cases h0 : G.dist r p / 2 % 2 = 0
      · simp [h0]; omega
      · simp [h0]; omega
    have hlab : ∀ w, pairLabel f (fun u _ => L u) b w = L w := by
      intro w; simp [pairLabel, hb]
    show degX G _ b ∈ ({1} : Set ℕ)
    simp only [Set.mem_singleton_iff, degX, hlab]
    have hS : {w | G.Adj b w ∧ L w = true} = if L p then {p} else {c} := by
      ext w
      have hw : G.Adj b w ↔ w = p ∨ w = c := by
        rw [← mem_neighborSet, hN]; simp
      simp only [Set.mem_ofPred_eq, hw]
      cases hLp : L p <;> simp only [hLp, Bool.not_false, Bool.not_true] at hLpc
      · simp only [Bool.false_eq_true, ↓reduceIte, Set.mem_singleton_iff]
        constructor
        · rintro ⟨rfl | rfl, h2⟩
          · rw [hLp] at h2; exact absurd h2 (by simp)
          · rfl
        · rintro rfl; exact ⟨Or.inr rfl, hLpc⟩
      · simp only [↓reduceIte, Set.mem_singleton_iff]
        constructor
        · rintro ⟨rfl | rfl, h2⟩
          · rfl
          · rw [hLpc] at h2; exact absurd h2 (by simp)
        · rintro rfl; exact ⟨Or.inl rfl, hLp⟩
    rw [hS]; split_ifs <;> simp

/-! ### The hardest problem of VI.b always has a solution -/

/-- The hardest problem of family VI.b (`W = 010⁺`, `B = 0⁺10`) is solvable on every instance
(proof of Theorem 8.3). Root the tree at a leaf `ℓ` and put the edge `{u, b}` (`u` white) into
`X` iff `b` is the parent of `u`. (With the paper's convention that `X`-edges are oriented from
black to white, this orients the edges *away from* the leaf; the paper says "towards the leaf".) -/
theorem viHard_exists [Finite V] (d δ : ℕ) (hd : 2 ≤ d) (hδ : 2 ≤ δ) {G : SimpleGraph V}
    {f : V → Bool} (h : IsInstance G f) : ∃ x, IsSolution (viHard d δ hd hδ) G f x := by
  obtain ⟨hG, hf⟩ := h
  obtain ⟨r, hr⟩ := IsTree.exists_deg_le_one hG
  refine ⟨pairLabel f (fun u b => decide (G.dist r b + 1 = G.dist r u)),
    fun v w hvw => pairLabel_symm hf _ hvw, ?_, ?_⟩
  · intro u hu hdu
    simp only [viHard] at hdu ⊢
    have hur : u ≠ r := by rintro rfl; omega
    obtain ⟨p, -, -, hpar⟩ := IsTree.parentSet_eq hG (r := r) hur
    show degX G _ u ∈ ({1} : Set ℕ)
    rw [Set.mem_singleton_iff, degX]
    convert Set.ncard_singleton p
    rw [← hpar]; ext w; simp [pairLabel, hu]
  · intro b hb hdb
    simp only [viHard] at hdb ⊢
    have hbr : b ≠ r := by rintro rfl; omega
    obtain ⟨p, hp, -, hpar⟩ := IsTree.parentSet_eq hG (r := r) hbr
    have hch := IsTree.childSet_eq hG r b
    rw [hpar] at hch
    show degX G _ b ∈ ({δ - 1} : Set ℕ)
    rw [Set.mem_singleton_iff, degX]
    have : {w | G.Adj b w ∧ pairLabel f (fun u b => decide (G.dist r b + 1 = G.dist r u)) b w
        = true} = G.neighborSet b \ {p} := by
      rw [← hch]; ext w; simp [pairLabel, hb]
    rw [this, Set.ncard_sdiff_singleton_of_mem (show p ∈ G.neighborSet b from hp), ← hdb, deg]

/-! ### The upper bounds of Theorems 8.1 and 8.3 -/

/-- Theorem 8.1 of [Balliu et al.], upper bound: problems of families V.a and V.b can be solved
in `O(n)` rounds (here: `n = |V|` rounds). -/
theorem theorem_8_1_upper [Fintype V] {P : Problem} (hP : P.IsVa ∨ P.IsVb) :
    WhiteSolvable P V (Fintype.card V) := by
  refine whiteSolvable_card P fun G f hGf => ?_
  rcases hP with hP | hP
  · exact va_exists hP hGf
  · obtain ⟨x, hx⟩ := va_exists hP hGf.swap
    exact ⟨x, (isSolution_swap_iff P G f x).1 hx⟩

/-- Theorem 8.3 of [Balliu et al.]: problems of families VI.a and VI.b can be solved in `O(n)`
rounds (here: `n = |V|` rounds). -/
theorem theorem_8_3 [Fintype V] {P : Problem} (hP : P.IsVIa ∨ P.IsVIb) :
    WhiteSolvable P V (Fintype.card V) := by
  refine whiteSolvable_card P fun G f hGf => ?_
  rcases hP with hP | hP
  · have hc := hP.compl
    obtain ⟨y, hy⟩ := viHard_exists _ _ P.compl.two_le_d P.compl.two_le_δ hGf
    have hy' := hy.of_restriction hc.viHard_le
    refine ⟨complLabel y, ?_⟩
    rw [← isSolution_compl_iff]
    have e : complLabel (complLabel y) = y := by funext v w; simp [complLabel]
    rwa [e]
  · obtain ⟨x, hx⟩ := viHard_exists _ _ P.two_le_d P.two_le_δ hGf
    exact ⟨x, hx.of_restriction hP.viHard_le⟩

end Podc.BinaryLabeling
