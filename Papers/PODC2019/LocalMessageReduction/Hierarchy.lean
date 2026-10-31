import Podc.Foundations.Combinatorics.SimpleGraph.ClusterSpanner

/-!
# The cluster hierarchy of algorithm `Sampler` (Section 3, Lemma 4.5, Theorem 4.6)

Bitton, Emek, Izumi, Kutten. *Message Reduction in the LOCAL Model is a Free Lunch.* PODC 2019
(arXiv:1909.08369v1).

`Sampler` runs `Cluster_j` for `j = 0, …, k` on graphs `G_0 = G, G_1, …, G_k`, where `G_{j+1}` is the
cluster graph of `G_j` w.r.t. the clusters formed at level `j`. We model **an arbitrary outcome** of
the random choices: the deterministic content of the stretch analysis is that *every* outcome satisfying
the postconditions of the procedure (and the "whp" facts of Lemmas 4.2 and 4.3) gives a
`(2·3^k − 1)`-spanner.

## Representation

* A level-`j` node is identified with a vertex of `V` (its root: a level-`(j+1)` node is a level-`j`
  center, so inductively every node is an original vertex). `cl j x = some a` means that the original
  vertex `x` lies in the level-`j` cluster `C_j(a)`; `cl j x = none` means that `x` was in an
  unclustered node at some level `< j`.
* `merge j a` is the outcome of the second step of `Cluster_j` for the level-`j` node `a`: `some a` if
  `a` is a center, `some b` if `a` joined the cluster of the center `b`, `none` if `a` is unclustered.
* The edges of the multigraph `G_j` between level-`j` nodes `a` and `b` are the original edges of `G`
  between `C_j(a)` and `C_j(b)` (`cross j a b`); this is exactly the paper's `E_j(a, b)`, multiplicities
  included.
* `F j a` is the edge set `F_a` produced by the first step of `Cluster_j` for node `a`. The spanner is
  `S = ⋃_{j ≤ k} ⋃_a F j a`.
-/

namespace Podc.LocalMessageReduction

open SimpleGraph

variable {V : Type*}

/-- The level-`j` cluster of an original vertex, given the merge maps of levels `< j`:
`C_0(x) = {x}`, and `x` is in the level-`(j+1)` node into which its level-`j` node was merged. -/
def clusterOf (merge : ℕ → V → Option V) : ℕ → V → Option V
  | 0, x => some x
  | j + 1, x => (clusterOf merge j x).bind (merge j)

/-- `E_j(a, b)`: the edges of `G_j` between the level-`j` nodes `a` and `b`, i.e. the original edges
of `G` with one endpoint in `C_j(a)` and the other in `C_j(b)`. -/
def cross (G : SimpleGraph V) (merge : ℕ → V → Option V) (j : ℕ) (a b : V) : Set (Sym2 V) :=
  {e | ∃ x y, G.Adj x y ∧ clusterOf merge j x = some a ∧ clusterOf merge j y = some b ∧ e = s(x, y)}

/-- An outcome of algorithm `Sampler` with parameter `k` on the simple graph `G`: the merge maps and
center marks of the levels `j < k` and the edge sets `F_a` of all levels `j ≤ k`, subject to the
postconditions of procedure `Cluster_j` (Pseudocode 2) that hold for every outcome of the coins. -/
structure Run (G : SimpleGraph V) (k : ℕ) where
  /-- Second step of `Cluster_j`: `some a` (center), `some b` (joined center `b`), `none`
  (unclustered). -/
  merge : ℕ → V → Option V
  /-- The set `F_a` built by node `a` in the first step of `Cluster_j`. -/
  F : ℕ → V → Set (Sym2 V)
  /-- `a` was marked as a center in `Cluster_j`. -/
  center : ℕ → V → Prop
  /-- `F_a ⊆ E_j(a)`: every edge of `F_a` joins `C_j(a)` to another level-`j` cluster. -/
  F_sub : ∀ j a e, e ∈ F j a → ∃ b, b ≠ a ∧ e ∈ cross G merge j a b
  /-- A center forms its own cluster `C(a) = {a}` (line 17). -/
  merge_center : ∀ j < k, ∀ a x, clusterOf merge j x = some a → center j a → merge j a = some a
  /-- A non-center joins only a center `b` such that `F` contains an edge between them (line 19). -/
  merge_some : ∀ j < k, ∀ a b x, clusterOf merge j x = some a → merge j a = some b →
    (b = a ∧ center j a) ∨
      (center j b ∧ ¬ center j a ∧ ∃ c, ∃ e ∈ F j c, e ∈ cross G merge j a b)
  /-- A non-center with an `F`-edge to some center does join some center (lines 18–20). -/
  merge_ne_none : ∀ j < k, ∀ a b x, clusterOf merge j x = some a → ¬ center j a → center j b →
    b ≠ a → (∃ c, ∃ e ∈ F j c, e ∈ cross G merge j a b) → merge j a ≠ none

namespace Run

variable {G : SimpleGraph V} {k : ℕ} (R : Run G k)

/-- `cl j x = some a`: `x ∈ C_j(a)`. -/
abbrev cl (j : ℕ) (x : V) : Option V := clusterOf R.merge j x

/-- `a` is a node of `G_j`. -/
def IsNode (j : ℕ) (a : V) : Prop := ∃ x, R.cl j x = some a

/-- The output edge set `S` of `Sampler` (Pseudocode 1, line 4). -/
def S : Set (Sym2 V) := {e | ∃ j ≤ k, ∃ a, e ∈ R.F j a}

/-- The output spanner `H = (V, S)`. -/
def H : SimpleGraph V := SimpleGraph.fromEdgeSet R.S

/-- `b ∈ N̂_j(a)`: `b` was queried by `a`, i.e. `F_a` contains an edge of `E_j(a, b)`. -/
def Queried (j : ℕ) (a b : V) : Prop := b ≠ a ∧ ∃ e ∈ R.F j a, e ∈ cross G R.merge j a b

/-- `a` is *light* at level `j`: `N̂_j(a) = N_j(a)`, i.e. every neighbor of `a` in `G_j` is
queried. -/
def Light (j : ℕ) (a : V) : Prop :=
  ∀ b, b ≠ a → (cross G R.merge j a b).Nonempty → R.Queried j a b

lemma cl_zero (x : V) : R.cl 0 x = some x := rfl

lemma cl_succ (j : ℕ) (x : V) : R.cl (j + 1) x = (R.cl j x).bind (R.merge j) := rfl

lemma H_le : R.H ≤ G := by
  intro x y h
  rw [H, fromEdgeSet_adj] at h
  obtain ⟨⟨j, -, a, he⟩, -⟩ := h
  obtain ⟨b, -, x', y', hadj, -, -, hxy⟩ := R.F_sub j a _ he
  rw [Sym2.eq_iff] at hxy
  rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hadj
  · exact hadj.symm

lemma H_adj_of_mem {j : ℕ} (hj : j ≤ k) {a x y : V} (hxy : G.Adj x y) (he : s(x, y) ∈ R.F j a) :
    R.H.Adj x y := by
  rw [H, fromEdgeSet_adj]
  exact ⟨⟨j, hj, a, he⟩, hxy.ne⟩

/-! ### Walks inside a vertex set -/

/-- There is an `H`-walk from `x` to `y` of length at most `n` whose vertices all satisfy `P`. -/
def WalkIn (H : SimpleGraph V) (P : V → Prop) (x y : V) (n : ℕ) : Prop :=
  ∃ p : H.Walk x y, p.length ≤ n ∧ ∀ z ∈ p.support, P z

lemma WalkIn.refl {H : SimpleGraph V} {P : V → Prop} {x : V} (hx : P x) (n : ℕ) :
    WalkIn H P x x n :=
  ⟨Walk.nil, by simp, by simpa using hx⟩

lemma WalkIn.adj {H : SimpleGraph V} {P : V → Prop} {x y : V} (h : H.Adj x y) (hx : P x)
    (hy : P y) : WalkIn H P x y 1 :=
  ⟨Walk.cons h Walk.nil, by simp, by simp [hx, hy]⟩

lemma WalkIn.symm {H : SimpleGraph V} {P : V → Prop} {x y : V} {n : ℕ} (h : WalkIn H P x y n) :
    WalkIn H P y x n := by
  obtain ⟨p, hl, hs⟩ := h
  exact ⟨p.reverse, by simpa using hl, by simpa using hs⟩

lemma WalkIn.trans {H : SimpleGraph V} {P : V → Prop} {x y z : V} {m n : ℕ}
    (h₁ : WalkIn H P x y m) (h₂ : WalkIn H P y z n) : WalkIn H P x z (m + n) := by
  obtain ⟨p, hp, hps⟩ := h₁
  obtain ⟨q, hq, hqs⟩ := h₂
  refine ⟨p.append q, by simp; omega, fun w hw => ?_⟩
  rw [Walk.mem_support_append_iff] at hw
  exact hw.elim (hps w) (hqs w)

lemma WalkIn.mono {H : SimpleGraph V} {P Q : V → Prop} {x y : V} {m n : ℕ}
    (h : WalkIn H P x y m) (hPQ : ∀ z, P z → Q z) (hmn : m ≤ n) : WalkIn H Q x y n := by
  obtain ⟨p, hp, hps⟩ := h
  exact ⟨p, hp.trans hmn, fun z hz => hPQ z (hps z hz)⟩

/-! ### Lemma 4.5: cluster diameter -/

/-- If the level-`j` node `a'` was merged into `a` (`j < k`), then `a` is a center, and `C_j(a')`
and `C_j(a)` are joined by an `H`-walk of length `≤ 1` (an edge of `F`, or nothing if `a' = a`). -/
lemma merge_connector {j : ℕ} (hj : j < k) {a' a x : V} (hx : R.cl j x = some a')
    (hm : R.merge j a' = some a) :
    R.merge j a = some a ∧ ∃ p q, R.cl j p = some a' ∧ R.cl j q = some a ∧
      WalkIn R.H (fun z => R.cl j z = some a' ∨ R.cl j z = some a) p q 1 := by
  rcases R.merge_some j hj a' a x hx hm with ⟨rfl, -⟩ | ⟨hc, -, c, e, he, hcross⟩
  · exact ⟨hm, x, x, hx, hx, WalkIn.refl (P := fun z => R.cl j z = some a ∨ R.cl j z = some a) (Or.inl hx) 1⟩
  · obtain ⟨p, q, hpq, hp, hq, rfl⟩ := hcross
    refine ⟨R.merge_center j hj a q hq hc, p, q, hp, hq, ?_⟩
    exact WalkIn.adj (R.H_adj_of_mem hj.le hpq he) (Or.inl hp) (Or.inr hq)

/-- **Lemma 4.5.** For every level `j ≤ k` and node `a ∈ V_j`, the cluster `C_j(a)` has diameter at
most `3^j − 1` in `Ind_H(C_j(a))`: any two of its vertices are joined by an `H`-walk of length
`≤ 3^j − 1` that stays inside `C_j(a)`. -/
theorem lemma_4_5 : ∀ j ≤ k, ∀ a x y, R.cl j x = some a → R.cl j y = some a →
    WalkIn R.H (fun z => R.cl j z = some a) x y (3 ^ j - 1) := by
  intro j
  induction j with
  | zero =>
    intro _ a x y hx hy
    simp only [cl_zero, Option.some.injEq] at hx hy
    subst hx hy
    exact ⟨Walk.nil, by simp, by simp [cl_zero]⟩
  | succ j ih =>
    intro hj a x y hx hy
    have hjk : j < k := hj
    rw [cl_succ, Option.bind_eq_some_iff] at hx hy
    obtain ⟨a', hxa', hma'⟩ := hx
    obtain ⟨b', hyb', hmb'⟩ := hy
    obtain ⟨hma, p, q, hp, hq, hpq⟩ := R.merge_connector hjk hxa' hma'
    obtain ⟨-, p', q', hp', hq', hpq'⟩ := R.merge_connector hjk hyb' hmb'
    -- every vertex in `C_j(a')`, `C_j(a)` or `C_j(b')` lies in `C_{j+1}(a)`
    have lift : ∀ z, (R.cl j z = some a' ∨ R.cl j z = some a ∨ R.cl j z = some b') →
        R.cl (j + 1) z = some a := by
      intro z hz
      rw [cl_succ]
      rcases hz with h | h | h <;> rw [h] <;> assumption
    have w1 := (ih hjk.le a' x p hxa' hp).mono (fun z hz => lift z (Or.inl hz)) le_rfl
    have w2 := hpq.mono (fun z hz => lift z (hz.elim Or.inl (fun h => Or.inr (Or.inl h)))) le_rfl
    have w3 := (ih hjk.le a q q' hq hq').mono (fun z hz => lift z (Or.inr (Or.inl hz))) le_rfl
    have w4 := hpq'.symm.mono
      (fun z hz => lift z (hz.elim (fun h => Or.inr (Or.inr h)) (fun h => Or.inr (Or.inl h))))
      le_rfl
    have w5 := (ih hjk.le b' p' y hp' hyb').mono (fun z hz => lift z (Or.inr (Or.inr hz))) le_rfl
    refine ((((w1.trans w2).trans w3).trans w4).trans w5).mono (fun _ h => h) ?_
    have h3 : 1 ≤ 3 ^ j := Nat.one_le_pow _ _ (by norm_num)
    rw [pow_succ]
    omega

/-! ### Theorem 4.6: stretch -/

/-- The level of the final cluster of `x`: the largest `r ≤ k` with `x` still in some level-`r`
node (the paper's `r(v)` for the unclustered node containing `x`). -/
noncomputable def lvl (x : V) : ℕ :=
  open Classical in Nat.findGreatest (fun j => (R.cl j x).isSome) k

/-- The final cluster of `x` in the partition `𝒞 = {C(v) | v ∈ V'}` of the proof of Theorem 4.6:
the pair `(r(v), v)` for the unclustered node `v ∋ x`. -/
noncomputable def label (x : V) : ℕ × Option V := (R.lvl x, R.cl (R.lvl x) x)

lemma lvl_le (x : V) : R.lvl x ≤ k := Nat.findGreatest_le _

lemma isSome_of_le {i j : ℕ} {x : V} (hij : i ≤ j) (h : (R.cl j x).isSome) :
    (R.cl i x).isSome := by
  induction j, hij using Nat.le_induction with
  | base => exact h
  | succ j _ ih =>
    apply ih
    rw [cl_succ] at h
    cases hc : R.cl j x with
    | none => simp [hc] at h
    | some _ => rfl

lemma isSome_lvl (x : V) : (R.cl (R.lvl x) x).isSome := by
  classical
  exact Nat.findGreatest_spec (P := fun j => (R.cl j x).isSome) (Nat.zero_le k) rfl

lemma isSome_of_le_lvl {i : ℕ} {x : V} (h : i ≤ R.lvl x) : (R.cl i x).isSome :=
  R.isSome_of_le h (R.isSome_lvl x)

lemma le_lvl {i : ℕ} {x : V} (hi : i ≤ k) (h : (R.cl i x).isSome) : i ≤ R.lvl x := by
  classical
  exact Nat.le_findGreatest (P := fun j => (R.cl j x).isSome) hi h

lemma cl_eq_of_le {i j : ℕ} {x y : V} (hij : i ≤ j) (h : R.cl i x = R.cl i y) :
    R.cl j x = R.cl j y := by
  induction j, hij using Nat.le_induction with
  | base => exact h
  | succ j _ ih => rw [cl_succ, cl_succ, ih]

/-- Vertices in the same level-`i` cluster, with `i` not above the final level of `x`, have the same
final cluster. -/
lemma label_eq_of_cl_eq {i : ℕ} {x y : V} (hi : i ≤ R.lvl x) (h : R.cl i x = R.cl i y) :
    R.label x = R.label y := by
  have hik : i ≤ k := hi.trans (R.lvl_le x)
  have hiy : i ≤ R.lvl y := R.le_lvl hik (h ▸ R.isSome_of_le_lvl hi)
  have key : ∀ {u w : V}, i ≤ R.lvl u → R.cl i u = R.cl i w → R.lvl w ≤ R.lvl u := by
    intro u w hu huw
    by_contra hlt
    push Not at hlt
    have hw := R.isSome_lvl w
    rw [← R.cl_eq_of_le (le_trans hu hlt.le) huw] at hw
    exact absurd (R.le_lvl (R.lvl_le w) hw) (by omega)
  have hl : R.lvl x = R.lvl y := le_antisymm (key hiy h.symm) (key hi h)
  simp only [label, hl, Prod.mk.injEq, true_and]
  exact R.cl_eq_of_le (hl ▸ hi) h

/-- Lemmas 4.2 + 4.3 (deterministic consequence): every unclustered node is light. -/
lemma light_of_unclustered
    (h43 : ∀ j < k, ∀ a, R.IsNode j a → R.Light j a ∨ ∃ b, R.Queried j a b ∧ R.center j b)
    {j : ℕ} (hj : j < k) {a x : V} (hx : R.cl j x = some a) (hm : R.merge j a = none) :
    R.Light j a := by
  rcases h43 j hj a ⟨x, hx⟩ with h | ⟨b, ⟨hba, e, he, hcr⟩, hcb⟩
  · exact h
  · have hca : ¬ R.center j a := fun hc => by
      rw [R.merge_center j hj a x hx hc] at hm; simp at hm
    exact absurd hm (R.merge_ne_none j hj a b x hx hca hcb hba ⟨a, e, he, hcr⟩)

/-- **Theorem 4.6** (deterministic core). Suppose the conclusions of Lemmas 4.2 and 4.3 hold in a run
of `Sampler`: at every level `j < k` every node is light or has queried some center, and every node of
`G_k` is light. Then `H = (V, S)` is a `(2·3^k − 1)`-spanner of `G`. (The paper states `O(2·3^k − 1)`;
the constant is exactly `2·3^k − 1`.) -/
theorem theorem_4_6
    (h43 : ∀ j < k, ∀ a, R.IsNode j a → R.Light j a ∨ ∃ b, R.Queried j a b ∧ R.center j b)
    (hk : ∀ a, R.IsNode k a → R.Light k a) :
    G.IsSpanner R.H (2 * 3 ^ k - 1) := by
  have h3 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have hst : 2 * 3 ^ k - 1 = 2 * (3 ^ k - 1) + 1 := by omega
  rw [hst]
  -- the final cluster of every vertex is light at its level
  have hlight : ∀ x, ∃ u, R.cl (R.lvl x) x = some u ∧ R.Light (R.lvl x) u := by
    intro x
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (R.isSome_lvl x)
    refine ⟨u, hu, ?_⟩
    rcases (R.lvl_le x).lt_or_eq with hlt | heq
    · apply R.light_of_unclustered h43 hlt hu
      have hnot : ¬ (R.cl (R.lvl x + 1) x).isSome := fun h => by
        have := R.le_lvl hlt h; omega
      rw [cl_succ, hu] at hnot
      simpa using hnot
    · rw [heq] at hu ⊢; exact hk u ⟨x, hu⟩
  -- the cross condition, for `lvl x ≤ lvl y`
  have hcross : ∀ x y, G.Adj x y → R.label x ≠ R.label y → R.lvl x ≤ R.lvl y →
      ∃ x' y', R.label x' = R.label x ∧ R.label y' = R.label y ∧ R.H.Adj x' y' := by
    intro x y hxy hne hle
    obtain ⟨u, hu, hlu⟩ := hlight x
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (R.isSome_of_le_lvl hle)
    have huw : w ≠ u := by
      rintro rfl
      exact hne (R.label_eq_of_cl_eq le_rfl (hu.trans hw.symm))
    obtain ⟨_, p, hpf, hpc⟩ := hlu w huw ⟨s(x, y), x, y, hxy, hu, hw, rfl⟩
    obtain ⟨p', q', hpq, hp, hq, rfl⟩ := hpc
    refine ⟨p', q', ?_, ?_, R.H_adj_of_mem (R.lvl_le x) hpq hpf⟩
    · exact (R.label_eq_of_cl_eq le_rfl (hu.trans hp.symm)).symm
    · exact (R.label_eq_of_cl_eq hle (hw.trans hq.symm)).symm
  refine SimpleGraph.isSpanner_of_clusters R.label (3 ^ k - 1) R.H_le ?_ ?_
  · intro x y hxy
    simp only [label, Prod.mk.injEq] at hxy
    obtain ⟨hl, hc⟩ := hxy
    obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp (R.isSome_lvl x)
    obtain ⟨p, hp, -⟩ := R.lemma_4_5 (R.lvl x) (R.lvl_le x) u x y hu (hl ▸ hc ▸ hu)
    calc R.H.edist x y ≤ p.length := edist_le p
      _ ≤ ((3 ^ k - 1 : ℕ) : ℕ∞) := by
        have : 3 ^ R.lvl x ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (R.lvl_le x)
        exact_mod_cast (by omega)
  · intro x y hxy hne
    rcases le_total (R.lvl x) (R.lvl y) with hle | hle
    · exact hcross x y hxy hne hle
    · obtain ⟨y', x', hy', hx', hadj⟩ := hcross y x hxy.symm (Ne.symm hne) hle
      exact ⟨x', y', hx', hy', hadj.symm⟩

/-! ### Non-vacuity -/

/-- A run satisfying all axioms: no node is a center, and every node queries all its neighbours
(this is what happens if every node is light and no center is drawn). -/
def trivialRun (G : SimpleGraph V) (k : ℕ) : Run G k where
  merge := fun _ _ => none
  F := fun j a => {e | ∃ b, b ≠ a ∧ e ∈ cross G (fun _ _ => none) j a b}
  center := fun _ _ => False
  F_sub := fun _ _ _ he => he
  merge_center := fun _ _ _ _ _ h => h.elim
  merge_some := fun _ _ _ _ _ _ h => by simp at h
  merge_ne_none := fun _ _ _ _ _ _ h => h.elim

/-- The hypotheses of Theorem 4.6 are satisfiable. -/
example (G : SimpleGraph V) (k : ℕ) : G.IsSpanner (trivialRun G k).H (2 * 3 ^ k - 1) := by
  have hl : ∀ j a, (trivialRun G k).Light j a := by
    intro j a b hb ⟨e, he⟩
    exact ⟨hb, e, ⟨b, hb, he⟩, he⟩
  exact (trivialRun G k).theorem_4_6 (fun j _ a _ => Or.inl (hl j a)) (fun a _ => hl k a)

end Run

end Podc.LocalMessageReduction
