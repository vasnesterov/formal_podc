import Papers.PODC2026.SinklessOrientation.Basic
import Podc.Foundations.Combinatorics.SimpleGraph.BFSTree

/-!
# Lemma 2.3: removing the `δ`-sinks of a sinksparse orientation (Algorithm 2)

Every `δ`-sink `s` looks at its distance-`h` neighbourhood (`h = k/2`) and its BFS tree, given by
the canonical parent pointers `bfsParent G s` (towards `s`; the parent of a node is *some* neighbour
one step closer to `s`, chosen by a fixed choice function, i.e. deterministically from the node
names).

* If the ball contains a node `t` of degree `< δ` (`lowSet`), the tree path from `s` to `t` is
  oriented towards `t` (`RepPath`).
* Otherwise the ball contains a node `t` with a neighbour `t'` that is not farther from `s` and is
  not the parent of `t` (`ntSet`; exists iff the ball contains a cycle). Let `v` be the
  highest-depth common ancestor of `t` and `t'`. We orient the tree path `s → t`, the edge
  `t → t'` and the tree path from `t'` up to `v` (`RepCycle`). This orients the cycle
  `v → … → t → t' → … → v` consistently and the path from `s` to the cycle towards the cycle
  (Figure 1 of the paper).

The repairs of all `δ`-sinks are applied simultaneously on top of the input orientation
(`repairOrientation`); to make the construction total even without the separation hypothesis,
an edge claimed in both directions keeps its old orientation.

## Main results

* `lemma_2_3_core` / `lemma_2_3` (**Lemma 2.3**, correctness): if distinct `δ`-sinks are at
  distance `> 2h` and every `δ`-sink has a node of degree `< δ` or a cycle within distance `h`
  (here: `HasBackEdges`, converted from cycles in `Main.lean`), the repaired orientation has no
  `δ`-sink, and only edges inside the distance-`h` balls of `δ`-sinks change.
* `repairOrientation_isLocal` (**Lemma 2.3**, round complexity): the repaired orientation of an
  edge `uv` only depends on the radius-`(2h+1)` view of `u` (graph and input orientation), i.e. the
  transformation takes `2h + 1 = O(k)` LOCAL rounds.
-/

namespace SinklessOrientation

open SimpleGraph
open Cslib.Local (GAgree)

variable {V : Type*}

lemma OAgree.symm {G G' : SimpleGraph V} {o : Orientation G} {o' : Orientation G'} {u : V} {R : ℕ}
    (hA : GAgree G G' u R) (hO : OAgree o o' u R) : OAgree o' o u R := by
  intro x hx y
  exact (hO ((hA.edist_lt_iff le_rfl).1 hx) y).symm

/-! ### The repair of one sink -/

section Repair

variable (G : SimpleGraph V) (δ h : ℕ) (s : V)

/-- Nodes of degree `< δ` within distance `h` of `s`. -/
def lowSet : Set V := {t | G.edist s t ≤ h ∧ deg G t < δ}

/-- Non-tree edges `(t, t')` of the ball: `t` is within distance `h` of `s`, `t'` is a neighbour of
`t` not farther from `s` and different from the parent of `t`. -/
def ntSet : Set (V × V) :=
  {p | G.edist s p.1 ≤ h ∧ G.Adj p.1 p.2 ∧ G.dist s p.2 ≤ G.dist s p.1 ∧ p.2 ≠ bfsParent G s p.1}

/-- The chosen node of low degree. -/
noncomputable def lowPick : V := @Classical.epsilon V ⟨s⟩ (· ∈ lowSet G δ h s)

/-- The chosen non-tree edge. -/
noncomputable def ntPick : V × V := @Classical.epsilon (V × V) ⟨(s, s)⟩ (· ∈ ntSet G h s)

/-- The number of steps from `t'` up to its highest-depth common ancestor with `t`. -/
noncomputable def lcaIdx (t t' : V) : ℕ :=
  sInf {j | j ≤ G.dist s t' ∧ ∃ i ≤ G.dist s t, bfsAncestor G s t' j = bfsAncestor G s t i}

/-- The tree path from `s` to `t`, oriented towards `t`. -/
def RepPath (t a b : V) : Prop :=
  ∃ i < G.dist s t, a = bfsAncestor G s t (i + 1) ∧ b = bfsAncestor G s t i

/-- The tree path from `s` to `t`, the edge `t → t'`, and the tree path from `t'` up to the
common ancestor of `t` and `t'`. -/
def RepCycle (t t' a b : V) : Prop :=
  RepPath G s t a b ∨ (a = t ∧ b = t') ∨
    ∃ j < lcaIdx G s t t', a = bfsAncestor G s t' j ∧ b = bfsAncestor G s t' (j + 1)

/-- The edges (with their new directions) reoriented by the sink `s` (Algorithm 2). -/
def repair (a b : V) : Prop :=
  ((lowSet G δ h s).Nonempty ∧ RepPath G s (lowPick G δ h s) a b) ∨
    (¬ (lowSet G δ h s).Nonempty ∧ (ntSet G h s).Nonempty ∧
      RepCycle G s (ntPick G h s).1 (ntPick G h s).2 a b)

variable {G δ h s}

lemma lowPick_mem (hne : (lowSet G δ h s).Nonempty) : lowPick G δ h s ∈ lowSet G δ h s :=
  @Classical.epsilon_spec V _ hne

lemma ntPick_mem (hne : (ntSet G h s).Nonempty) : ntPick G h s ∈ ntSet G h s :=
  @Classical.epsilon_spec (V × V) _ hne

section Facts

variable {t t' : V}

lemma lcaIdx_mem (hr : G.Reachable s t) (hr' : G.Reachable s t') :
    lcaIdx G s t t' ≤ G.dist s t' ∧
      ∃ i ≤ G.dist s t, bfsAncestor G s t' (lcaIdx G s t t') = bfsAncestor G s t i :=
  Nat.sInf_mem
    (s := {j | j ≤ G.dist s t' ∧ ∃ i ≤ G.dist s t, bfsAncestor G s t' j = bfsAncestor G s t i})
    ⟨G.dist s t', le_rfl, G.dist s t, le_rfl,
      by rw [hr'.bfsAncestor_eq_root le_rfl, hr.bfsAncestor_eq_root le_rfl]⟩

lemma lcaIdx_le_of {j i : ℕ} (hj : j ≤ G.dist s t') (hi : i ≤ G.dist s t)
    (he : bfsAncestor G s t' j = bfsAncestor G s t i) : lcaIdx G s t t' ≤ j :=
  Nat.sInf_le ⟨hj, i, hi, he⟩

/-- An equality between ancestors forces equal depths. -/
lemma dist_eq_of_anc_eq {x y : V} (hx : G.Reachable s x) (hy : G.Reachable s y) {i j : ℕ}
    (he : bfsAncestor G s x i = bfsAncestor G s y j) : G.dist s x - i = G.dist s y - j := by
  rw [← hx.dist_bfsAncestor, ← hy.dist_bfsAncestor, he]

/-- Facts about a path repair rooted at a node `t` of the ball. -/
lemma repPath_adj (hr : G.Reachable s t) {a b : V} (hab : RepPath G s t a b) : G.Adj a b := by
  obtain ⟨i, hi, rfl, rfl⟩ := hab
  exact (hr.adj_bfsAncestor hi).symm

lemma repPath_not_symm (hr : G.Reachable s t) {a b : V} (h1 : RepPath G s t a b)
    (h2 : RepPath G s t b a) : False := by
  obtain ⟨i, hi, rfl, rfl⟩ := h1
  obtain ⟨i', hi', h3, h4⟩ := h2
  have e1 := dist_eq_of_anc_eq hr hr h3
  have e2 := dist_eq_of_anc_eq hr hr h4
  omega

lemma repPath_mem {a b : V} (hab : RepPath G s t a b) :
    (∃ m ≤ G.dist s t, a = bfsAncestor G s t m) ∧ (∃ m ≤ G.dist s t, b = bfsAncestor G s t m) := by
  obtain ⟨i, hi, rfl, rfl⟩ := hab
  exact ⟨⟨i + 1, hi, rfl⟩, ⟨i, hi.le, rfl⟩⟩

lemma repPath_out {m : ℕ} (hm : m ≤ G.dist s t) (hm0 : m ≠ 0) :
    RepPath G s t (bfsAncestor G s t m) (bfsAncestor G s t (m - 1)) :=
  ⟨m - 1, by omega, by rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm0)], rfl⟩

lemma ntSet_reachable (hp : (t, t') ∈ ntSet G h s) : G.Reachable s t ∧ G.Reachable s t' :=
  ⟨reachable_of_edist_le_natCast hp.1, (reachable_of_edist_le_natCast hp.1).trans hp.2.1.reachable⟩

lemma ntSet_ne (hp : (t, t') ∈ ntSet G h s) : t ≠ s := by
  rintro rfl
  have h1 := hp.2.2.1
  simp only [dist_self, nonpos_iff_eq_zero] at h1
  rw [(ntSet_reachable hp).2.dist_eq_zero_iff] at h1
  exact hp.2.1.ne h1

lemma repCycle_adj (hp : (t, t') ∈ ntSet G h s) {a b : V} (hab : RepCycle G s t t' a b) :
    G.Adj a b := by
  obtain ⟨hr, hr'⟩ := ntSet_reachable hp
  rcases hab with hab | ⟨rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩
  · exact repPath_adj hr hab
  · exact hp.2.1
  · exact hr'.adj_bfsAncestor (lt_of_lt_of_le hj (lcaIdx_mem hr hr').1)

lemma repCycle_not_symm (hp : (t, t') ∈ ntSet G h s) {a b : V} (h1 : RepCycle G s t t' a b)
    (h2 : RepCycle G s t t' b a) : False := by
  obtain ⟨hr, hr'⟩ := ntSet_reachable hp
  have hpos : 0 < G.dist s t := hr.pos_dist_of_ne (ntSet_ne hp).symm
  obtain ⟨_, hadj, hdd, hpar⟩ := hp
  replace hdd : G.dist s t' ≤ G.dist s t := hdd
  replace hadj : G.Adj t t' := hadj
  replace hpar : t' ≠ bfsParent G s t := hpar
  have hL := lcaIdx_mem hr hr'
  have hpar1 : bfsAncestor G s t 1 = bfsParent G s t := rfl
  rcases h1 with h1 | ⟨rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩
  · obtain ⟨i, hi, rfl, rfl⟩ := h1
    rcases h2 with h2 | ⟨h3, h4⟩ | ⟨j, hj, h3, h4⟩
    · exact repPath_not_symm hr ⟨i, hi, rfl, rfl⟩ h2
    · -- `anc t i = t` and `t' = anc t (i+1)`: then `i = 0` and `t' = par t`
      have e := dist_eq_of_anc_eq hr hr (i := i) (j := 0) h3
      have hi0 : i = 0 := by omega
      subst hi0; exact hpar (h4.symm.trans hpar1)
    · have := lcaIdx_le_of (t := t) (t' := t') (by
        have := dist_eq_of_anc_eq hr' hr h3.symm; omega) hi.le h3.symm
      omega
  · rcases h2 with h2 | ⟨h3, _⟩ | ⟨j, hj, h3, h4⟩
    · obtain ⟨i, hi, h3, h4⟩ := h2
      have e := dist_eq_of_anc_eq hr hr (i := 0) (j := i) h4
      have hi0 : i = 0 := by omega
      subst hi0; exact hpar (h3.trans hpar1)
    · exact hadj.ne h3.symm
    · have e := dist_eq_of_anc_eq hr' hr' (i := 0) (j := j) h3
      have e2 := dist_eq_of_anc_eq hr hr' (i := 0) (j := j + 1) h4
      omega
  · rcases h2 with h2 | ⟨h3, h4⟩ | ⟨j', hj', h3, h4⟩
    · obtain ⟨i, hi, h3, h4⟩ := h2
      have := lcaIdx_le_of (t := t) (t' := t') (by omega) (Nat.le_of_lt_succ (by omega) : i ≤ _)
        h4
      omega
    · have e := dist_eq_of_anc_eq hr' hr' (i := j) (j := 0) h4
      have e2 := dist_eq_of_anc_eq hr' hr (i := j + 1) (j := 0) h3
      omega
    · have e1 := dist_eq_of_anc_eq hr' hr' h3
      have e2 := dist_eq_of_anc_eq hr' hr' h4
      omega

end Facts

/-- Edges of a repair are edges of `G` inside the distance-`h` ball of `s`. -/
lemma repair_adj_mem {a b : V} (hab : repair G δ h s a b) :
    G.Adj a b ∧ G.edist s a ≤ h ∧ G.edist s b ≤ h := by
  rcases hab with ⟨hne, hab⟩ | ⟨_, hne, hab⟩
  · have ht := (lowPick_mem hne).1
    have hr := reachable_of_edist_le_natCast ht
    refine ⟨repPath_adj hr hab, ?_, ?_⟩
    · obtain ⟨⟨m, -, rfl⟩, -⟩ := repPath_mem hab; exact edist_bfsAncestor_le ht m
    · obtain ⟨-, ⟨m, -, rfl⟩⟩ := repPath_mem hab; exact edist_bfsAncestor_le ht m
  · have hp := ntPick_mem hne
    set t := (ntPick G h s).1
    set t' := (ntPick G h s).2
    have hp' : (t, t') ∈ ntSet G h s := hp
    obtain ⟨hr, hr'⟩ := ntSet_reachable hp'
    have ht : G.edist s t ≤ h := hp.1
    have ht' : G.edist s t' ≤ h := by
      apply hr'.edist_le_natCast
      exact hp.2.2.1.trans (dist_le_of_edist_le_natCast ht)
    refine ⟨repCycle_adj hp' hab, ?_⟩
    rcases hab with hab | ⟨rfl, rfl⟩ | ⟨j, -, rfl, rfl⟩
    · obtain ⟨⟨m, -, rfl⟩, ⟨m', -, rfl⟩⟩ := repPath_mem hab
      exact ⟨edist_bfsAncestor_le ht m, edist_bfsAncestor_le ht m'⟩
    · exact ⟨ht, ht'⟩
    · exact ⟨edist_bfsAncestor_le ht' j, edist_bfsAncestor_le ht' (j + 1)⟩

lemma repair_not_symm {a b : V} (h1 : repair G δ h s a b) (h2 : repair G δ h s b a) : False := by
  rcases h1 with ⟨hne, h1⟩ | ⟨hlow, hne, h1⟩
  · rcases h2 with ⟨-, h2⟩ | ⟨hlow, -⟩
    · exact repPath_not_symm (reachable_of_edist_le_natCast (lowPick_mem hne).1) h1 h2
    · exact hlow hne
  · rcases h2 with ⟨hne', -⟩ | ⟨-, -, h2⟩
    · exact hlow hne'
    · exact repCycle_not_symm (ntPick_mem hne) h1 h2

/-- Coverage: in the presence of a node of degree `< δ` or of a non-tree edge, the sink `s` gets an
outgoing repaired edge, and every node touched by the repair either gets an outgoing repaired edge
or has degree `< δ`. -/
lemma repair_cover (hs : δ ≤ deg G s)
    (hgood : (∃ t, G.edist s t ≤ h ∧ deg G t < δ) ∨ (ntSet G h s).Nonempty) :
    (∃ c, repair G δ h s s c) ∧
      ∀ a b, (repair G δ h s a b ∨ repair G δ h s b a) → (∃ c, repair G δ h s a c) ∨ deg G a < δ := by
  by_cases hlow : (lowSet G δ h s).Nonempty
  · have ht := lowPick_mem hlow
    set t := lowPick G δ h s
    have hr := reachable_of_edist_le_natCast ht.1
    have hts : t ≠ s := fun e => by have := ht.2; rw [e] at this; omega
    have hpos : G.dist s t ≠ 0 := (hr.pos_dist_of_ne hts.symm).ne'
    -- every node `anc t m` with `m ≥ 1` has an outgoing edge
    have hcov : ∀ m ≤ G.dist s t, m ≠ 0 → ∃ c, repair G δ h s (bfsAncestor G s t m) c :=
      fun m hm hm0 => ⟨_, Or.inl ⟨hlow, repPath_out hm hm0⟩⟩
    refine ⟨?_, ?_⟩
    · have := hcov _ le_rfl hpos
      rwa [hr.bfsAncestor_eq_root le_rfl] at this
    · intro a b hab
      have hpath : ∃ m ≤ G.dist s t, a = bfsAncestor G s t m := by
        rcases hab with (⟨-, hab⟩ | ⟨hl, -⟩) | (⟨-, hab⟩ | ⟨hl, -⟩)
        · exact (repPath_mem hab).1
        · exact absurd hlow hl
        · exact (repPath_mem hab).2
        · exact absurd hlow hl
      obtain ⟨m, hm, rfl⟩ := hpath
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · exact Or.inr ht.2
      · exact Or.inl (hcov m hm hm0.ne')
  · have hne : (ntSet G h s).Nonempty := by
      rcases hgood with ⟨t, ht⟩ | hne
      · exact absurd ⟨t, ht⟩ hlow
      · exact hne
    have hp := ntPick_mem hne
    set t := (ntPick G h s).1
    set t' := (ntPick G h s).2
    have hp' : (t, t') ∈ ntSet G h s := hp
    obtain ⟨hr, hr'⟩ := ntSet_reachable hp'
    have hpos : G.dist s t ≠ 0 := (hr.pos_dist_of_ne (ntSet_ne hp').symm).ne'
    have hL := lcaIdx_mem hr hr'
    have rep : ∀ a b, RepCycle G s t t' a b → repair G δ h s a b :=
      fun a b hab => Or.inr ⟨hlow, hne, hab⟩
    -- nodes on the tree path `s → t` have outgoing edges
    have hcov : ∀ m ≤ G.dist s t, ∃ c, repair G δ h s (bfsAncestor G s t m) c := by
      intro m hm
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · exact ⟨t', rep _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · exact ⟨_, rep _ _ (Or.inl (repPath_out hm hm0.ne'))⟩
    -- nodes on the path from `t'` to the common ancestor have outgoing edges
    have hcov' : ∀ j ≤ lcaIdx G s t t', ∃ c, repair G δ h s (bfsAncestor G s t' j) c := by
      intro j hj
      rcases hj.lt_or_eq with hj | rfl
      · exact ⟨_, rep _ _ (Or.inr (Or.inr ⟨j, hj, rfl, rfl⟩))⟩
      · obtain ⟨i, hi, he⟩ := hL.2
        rw [he]; exact hcov i hi
    refine ⟨?_, ?_⟩
    · have := hcov _ le_rfl
      rwa [hr.bfsAncestor_eq_root le_rfl] at this
    · intro a b hab
      left
      have hab' : RepCycle G s t t' a b ∨ RepCycle G s t t' b a := by
        rcases hab with (⟨hl, -⟩ | ⟨-, -, hab⟩) | (⟨hl, -⟩ | ⟨-, -, hab⟩)
        · exact absurd hl hlow
        · exact Or.inl hab
        · exact absurd hl hlow
        · exact Or.inr hab
      rcases hab' with (hab | ⟨rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩) | (hab | ⟨rfl, rfl⟩ | ⟨j, hj, rfl, rfl⟩)
      · obtain ⟨⟨m, hm, rfl⟩, -⟩ := repPath_mem hab; exact hcov m hm
      · exact hcov 0 (Nat.zero_le _)
      · exact hcov' j hj.le
      · obtain ⟨-, ⟨m, hm, rfl⟩⟩ := repPath_mem hab; exact hcov m hm
      · exact hcov' 0 (Nat.zero_le _)
      · exact hcov' (j + 1) hj

end Repair

/-! ### Applying all repairs -/

section Orientation

variable {G : SimpleGraph V} (δ h : ℕ) (o : Orientation G)

/-- Some `δ`-sink of `o` reorients the edge `ab` as `a → b`. -/
def Fwd (a b : V) : Prop := ∃ s, o.IsDeltaSink δ s ∧ repair G δ h s a b

/-- The edge `ab` is reoriented, and the reorientations are not contradictory. -/
def Good (a b : V) : Prop := (Fwd δ h o a b ∨ Fwd δ h o b a) ∧ ¬ (Fwd δ h o a b ∧ Fwd δ h o b a)

lemma good_comm {a b : V} : Good δ h o a b ↔ Good δ h o b a := by
  unfold Good; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, fun h => h2 h.symm⟩

/-- The output of Algorithm 2: every `δ`-sink `s` of `o` applies its repair `repair G δ h s`. -/
noncomputable def repairOrientation : Orientation G where
  out a b := (Good δ h o a b ∧ Fwd δ h o a b) ∨ (¬ Good δ h o a b ∧ o.out a b)
  adj_of_out a b := by
    rintro (⟨-, s, -, hs⟩ | ⟨-, hab⟩)
    · exact (repair_adj_mem hs).1
    · exact o.adj_of_out hab
  out_or_out a b hab := by
    by_cases hg : Good δ h o a b
    · rcases hg.1 with h1 | h1
      · exact Or.inl (Or.inl ⟨hg, h1⟩)
      · exact Or.inr (Or.inl ⟨(good_comm δ h o).1 hg, h1⟩)
    · rcases o.out_or_out hab with h1 | h1
      · exact Or.inl (Or.inr ⟨hg, h1⟩)
      · exact Or.inr (Or.inr ⟨fun h' => hg ((good_comm δ h o).2 h'), h1⟩)
  not_out_of_out a b := by
    rintro (⟨hg, h1⟩ | ⟨hg, h1⟩) (⟨hg', h2⟩ | ⟨hg', h2⟩)
    · exact hg.2 ⟨h1, h2⟩
    · exact hg' ((good_comm δ h o).1 hg)
    · exact hg ((good_comm δ h o).2 hg')
    · exact o.not_out_of_out h1 h2

variable {δ h o}

lemma two_mul_lt_of_mem {s s' a : V} (ha : G.edist s a ≤ h) (ha' : G.edist s' a ≤ h)
    (hsep : ((2 * h : ℕ) : ℕ∞) < G.edist s s') : False := by
  have : G.edist s s' ≤ ((2 * h : ℕ) : ℕ∞) := by
    calc G.edist s s' ≤ G.edist s a + G.edist a s' := G.edist_triangle
      _ ≤ h + h := add_le_add ha (by rw [SimpleGraph.edist_comm]; exact ha')
      _ = ((2 * h : ℕ) : ℕ∞) := by push_cast; ring
  exact absurd hsep (not_lt.2 this)

/-- **Lemma 2.3** of [Nolin, PODC'26] (correctness, with the non-tree-edge form of the hypothesis):
if distinct `δ`-sinks of `o` are at distance `> 2h` and the distance-`h` ball of every `δ`-sink
contains a node of degree `< δ` or a non-tree edge, then after the repairs there is no `δ`-sink,
and only edges inside the distance-`h` balls of `δ`-sinks are changed. -/
theorem lemma_2_3_core
    (hsep : ∀ s s', o.IsDeltaSink δ s → o.IsDeltaSink δ s' → s ≠ s' →
      ((2 * h : ℕ) : ℕ∞) < G.edist s s')
    (hgood : ∀ s, o.IsDeltaSink δ s →
      (∃ t, G.edist s t ≤ h ∧ deg G t < δ) ∨ (ntSet G h s).Nonempty) :
    (repairOrientation δ h o).NoDeltaSink δ ∧
      ∀ a b, ((repairOrientation δ h o).out a b ↔ o.out a b) ∨
        ∃ s, o.IsDeltaSink δ s ∧ G.edist s a ≤ h ∧ G.edist s b ≤ h := by
  -- with separated sinks, the repairs never contradict each other
  have hgood' : ∀ a b, (Fwd δ h o a b ∨ Fwd δ h o b a) → Good δ h o a b := by
    intro a b hab
    refine ⟨hab, ?_⟩
    rintro ⟨⟨s, hs, h1⟩, ⟨s', hs', h2⟩⟩
    by_cases hss : s = s'
    · subst hss; exact repair_not_symm h1 h2
    · exact two_mul_lt_of_mem (repair_adj_mem h1).2.1 (repair_adj_mem h2).2.2 (hsep s s' hs hs' hss)
  refine ⟨?_, ?_⟩
  · rw [Orientation.noDeltaSink_iff]
    intro x hx
    by_cases htouch : ∃ s, o.IsDeltaSink δ s ∧ ∃ y, repair G δ h s x y ∨ repair G δ h s y x
    · obtain ⟨s, hs, y, hy⟩ := htouch
      rcases (repair_cover hs.2 (hgood s hs)).2 x y hy with ⟨c, hc⟩ | hlow
      · exact ⟨c, Or.inl ⟨hgood' x c (Or.inl ⟨s, hs, hc⟩), s, hs, hc⟩⟩
      · omega
    · push Not at htouch
      -- `x` is not a `δ`-sink of `o` (a `δ`-sink is touched by its own repair)
      have hns : ¬ o.IsDeltaSink δ x := by
        intro hs
        obtain ⟨c, hc⟩ := (repair_cover hs.2 (hgood x hs)).1
        exact (htouch x hs c).1 hc
      have : ¬ o.IsSink x := fun h' => hns ⟨h', hx⟩
      simp only [Orientation.IsSink, not_forall, not_not] at this
      obtain ⟨y, hy⟩ := this
      refine ⟨y, Or.inr ⟨?_, hy⟩⟩
      rintro ⟨⟨s, hs, h1⟩ | ⟨s, hs, h1⟩, -⟩
      · exact (htouch s hs y).1 h1
      · exact (htouch s hs y).2 h1
  · intro a b
    by_cases hg : Good δ h o a b
    · right
      rcases hg.1 with ⟨s, hs, h1⟩ | ⟨s, hs, h1⟩
      · exact ⟨s, hs, (repair_adj_mem h1).2⟩
      · exact ⟨s, hs, (repair_adj_mem h1).2.2, (repair_adj_mem h1).2.1⟩
    · left
      show (Good δ h o a b ∧ Fwd δ h o a b) ∨ (¬ Good δ h o a b ∧ o.out a b) ↔ o.out a b
      tauto

/-- From a `k`-sinksparse orientation with `2h ≤ k` the separation hypothesis of Lemma 2.3
follows. -/
lemma sep_of_isSinkSparse {k : ℕ} (hk : 2 * h ≤ k) (hsp : o.IsSinkSparse k) :
    ∀ s s', o.IsDeltaSink δ s → o.IsDeltaSink δ s' → s ≠ s' →
      ((2 * h : ℕ) : ℕ∞) < G.edist s s' :=
  fun s s' hs hs' hne => lt_of_le_of_lt (by exact_mod_cast hk) (hsp hs.1 hs'.1 hne)

end Orientation

/-! ### Locality of the repair -/

section Locality

variable {G G' : SimpleGraph V} {δ h : ℕ} {s : V}

lemma succ_le_succ_coe {e : ℕ∞} {h : ℕ} (he : e ≤ h) : e + 1 ≤ ((h + 1 : ℕ) : ℕ∞) := by
  push_cast; exact add_le_add_left he 1

/-- The repair of a sink `s` only depends on the edges at distance `≤ h` from `s`. -/
lemma repair_congr (hA : GAgree G G' s (h + 1)) (a b : V) :
    repair G' δ h s a b ↔ repair G δ h s a b := by
  have hle : ∀ x : V, G.edist s x ≤ h → G.edist s x ≤ (h + 1 : ℕ) :=
    fun x hx => hx.trans (by exact_mod_cast Nat.le_succ h)
  have hD : ∀ x, G.edist s x ≤ (h + 1 : ℕ) → G'.dist s x = G.dist s x :=
    fun x hx => hA.dist_eq hx
  have hBall : ∀ x, G'.edist s x ≤ h ↔ G.edist s x ≤ h := fun x => hA.edist_le_iff (by omega)
  have hAdj : ∀ x, G.edist s x ≤ h → ∀ y, G.Adj x y ↔ G'.Adj x y := by
    intro x hx y
    apply hA
    exact lt_of_le_of_lt hx (by exact_mod_cast Nat.lt_succ_self h)
  have hpar : ∀ x, G.edist s x ≤ h → bfsParent G' s x = bfsParent G s x := by
    intro x hx
    refine bfsParent_congr fun y _ => ?_
    constructor
    · rintro ⟨hxy, hd⟩
      have hxy' := (hAdj x hx y).2 hxy
      refine ⟨hxy', ?_⟩
      rw [← hD y ((edist_le_add_one_of_adj hxy').trans (succ_le_succ_coe hx)), ← hD x (hle x hx)]
      exact hd
    · rintro ⟨hxy, hd⟩
      refine ⟨(hAdj x hx y).1 hxy, ?_⟩
      rw [hD y ((edist_le_add_one_of_adj hxy).trans (succ_le_succ_coe hx)), hD x (hle x hx)]
      exact hd
  have hanc : ∀ x, G.edist s x ≤ h → ∀ i, bfsAncestor G' s x i = bfsAncestor G s x i := by
    intro x hx i
    induction i with
    | zero => rfl
    | succ i ih => rw [bfsAncestor_succ, bfsAncestor_succ, ih, hpar _ (edist_bfsAncestor_le hx i)]
  have hlow : lowSet G' δ h s = lowSet G δ h s := by
    ext t
    simp only [lowSet, Set.mem_ofPred_eq, hBall]
    apply and_congr_right; intro ht
    rw [deg_eq_of_gAgree (hA.mono (a := h) ht (by omega : h + 1 ≤ h + 1)) (by omega)]
  have hnt : ntSet G' h s = ntSet G h s := by
    ext ⟨t, t'⟩
    simp only [ntSet, Set.mem_ofPred_eq, hBall]
    apply and_congr_right; intro ht
    rw [← hAdj t ht t']
    apply and_congr_right; intro htt'
    rw [hD t (hle t ht), hD t' ((edist_le_add_one_of_adj htt').trans (succ_le_succ_coe ht)), hpar t ht]
  have hpath : ∀ t, G.edist s t ≤ h → ∀ a b, RepPath G' s t a b ↔ RepPath G s t a b := by
    intro t ht a b
    simp only [RepPath, hD t (hle t ht), hanc t ht]
  have hcyc : ∀ t t', (t, t') ∈ ntSet G h s → ∀ a b,
      RepCycle G' s t t' a b ↔ RepCycle G s t t' a b := by
    intro t t' hp a b
    have ht : G.edist s t ≤ h := hp.1
    have ht' : G.edist s t' ≤ h := by
      apply (ntSet_reachable hp).2.edist_le_natCast
      exact hp.2.2.1.trans (dist_le_of_edist_le_natCast ht)
    have hlca : lcaIdx G' s t t' = lcaIdx G s t t' := by
      simp only [lcaIdx, hD t (hle t ht), hD t' (hle t' ht'), hanc t ht, hanc t' ht']
    simp only [RepCycle, hpath t ht, hlca, hanc t' ht']
  unfold repair
  rw [show lowPick G' δ h s = lowPick G δ h s by simp only [lowPick, hlow],
    show ntPick G' h s = ntPick G h s by simp only [ntPick, hnt], hlow, hnt]
  apply or_congr
  · apply and_congr_right; intro hne
    exact hpath _ (lowPick_mem hne).1 a b
  · apply and_congr_right; intro _
    apply and_congr_right; intro hne
    exact hcyc _ _ (ntPick_mem hne) a b

lemma fwd_of_gAgree {o : Orientation G} {o' : Orientation G'} {u a b : V}
    (hA : GAgree G G' u (2 * h + 1)) (hO : OAgree o o' u (2 * h + 1)) (hu : u = a ∨ u = b)
    (hf : Fwd δ h o a b) : Fwd δ h o' a b := by
  obtain ⟨s, ⟨hsink, hdeg⟩, hrep⟩ := hf
  have hmem := (repair_adj_mem hrep).2
  have hus : G.edist u s ≤ h := by
    rw [SimpleGraph.edist_comm]; rcases hu with rfl | rfl
    · exact hmem.1
    · exact hmem.2
  have hAs : GAgree G G' s (h + 1) := hA.mono hus (by omega)
  refine ⟨s, ⟨?_, ?_⟩, (repair_congr hAs a b).2 hrep⟩
  · intro y hy
    exact hsink y ((hO (lt_of_le_of_lt hus (by exact_mod_cast (by omega : h < 2 * h + 1))) y).2 hy)
  · rw [← deg_eq_of_gAgree (hAs.mono_radius (by omega : 1 ≤ h + 1)) (by omega)]; exact hdeg

/-- **Lemma 2.3** of [Nolin, PODC'26] (round complexity): the repaired orientation of an edge `uv`
only depends on the graph and on the input orientation within distance `2h + 1` of `u`. Hence
Algorithm 2 takes `2h + 1 = O(k)` LOCAL rounds (for `h = k/2`). -/
theorem repairOrientation_isLocal :
    IsLocalRel (V := V) (fun G (o : Orientation G) => repairOrientation δ h o) (2 * h + 1) := by
  intro G G' o o' u hA hO v
  have hA' := hA.symm
  have hO' := hO.symm hA
  have hfwd : ∀ a b, (u = a ∨ u = b) → (Fwd δ h o a b ↔ Fwd δ h o' a b) := fun a b hu =>
    ⟨fwd_of_gAgree hA hO hu, fwd_of_gAgree hA' hO' hu⟩
  have h1 := hfwd u v (Or.inl rfl)
  have h2 := hfwd v u (Or.inr rfl)
  have hout : o.out u v ↔ o'.out u v := hO (by simp) v
  simp only [repairOrientation, Good, h1, h2, hout]

end Locality

end SinklessOrientation
