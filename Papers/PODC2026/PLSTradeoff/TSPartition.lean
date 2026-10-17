import Papers.PODC2026.PLSTradeoff.Basic

/-!
# Two-separated partitions and cluster-degeneracy (Section 3)

* `TSPartition G t ε` (Definition 2): a partition of `V` (given by the cluster map `cl`, with
  `v ∈ cl v` and `u ∈ cl v → cl u = cl v`) and a separating set `X`, such that every walk between
  non-`X` nodes of different clusters contains two consecutive `X` nodes, every cluster has weak
  diameter `≤ t`, and every cluster has cost ratio `|C ∩ X| / |C| ≤ ε`.
* `TSPartition.sep`: the two-separation property is equivalent to "non-`X` nodes of different
  clusters are at distance `> 2`" (`twoSep_iff`).
* `ClusterDegenerate`, `WeaklyBounded` (Definition 3) for an ordered partition given by a cluster
  index `idx : V → ℕ`, and Lemma 3.1 (`TSPartition.ofDegenerate`).
* Lemma 3.3 (`exists_ball_subset`), Lemma 3.4 (`hset_disjoint`).
* `TSOut`, `TSOut.Correct`, `TSCert` (Definition 4): a PLS that certifies and outputs a
  TS partition.
-/

namespace PLSTradeoff

open SimpleGraph SinklessOrientation

variable {V : Type*}

/-- The walk `p` contains two consecutive vertices of `X`. -/
def HasTwoConsecutive {G : SimpleGraph V} {u w : V} (p : G.Walk u w) (X : Set V) : Prop :=
  ∃ d ∈ p.darts, d.fst ∈ X ∧ d.snd ∈ X

/-- Definition 2: a `(t, ε)`-two-separated partition (TS partition) of `G`. -/
structure TSPartition (G : SimpleGraph V) (t : ℕ) (ε : ℝ) where
  /-- The cluster containing a node. -/
  cl : V → Set V
  mem_cl : ∀ v, v ∈ cl v
  cl_eq : ∀ u v, u ∈ cl v → cl u = cl v
  /-- The separating set. -/
  X : Set V
  /-- Two separation: every walk from a non-`X` node of one cluster to a non-`X` node of another
  cluster has two consecutive vertices in `X`. -/
  twoSep : ∀ u w (p : G.Walk u w), u ∉ X → w ∉ X → cl u ≠ cl w → HasTwoConsecutive p X
  /-- Bounded (weak) diameter. -/
  diam : ∀ v, ∀ a ∈ cl v, ∀ b ∈ cl v, G.edist a b ≤ t
  /-- Cost ratio `|C ∩ X| ≤ ε |C|` for every cluster `C`. -/
  ratio : ∀ v, ((cl v ∩ X).ncard : ℝ) ≤ ε * (cl v).ncard

section TwoSep

variable {G : SimpleGraph V}

lemma not_hasTwoConsecutive_of_length_le_two {u w : V} (p : G.Walk u w) (X : Set V)
    (hu : u ∉ X) (hw : w ∉ X) (hp : p.length ≤ 2) : ¬ HasTwoConsecutive p X := by
  rintro ⟨d, hd, h1, h2⟩
  match p, hp with
  | .nil, _ => simp at hd
  | .cons h .nil, _ =>
    simp only [Walk.darts_cons, Walk.darts_nil, List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd; exact hu h1
  | .cons h (.cons h' .nil), _ =>
    simp only [Walk.darts_cons, Walk.darts_nil, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl
    · exact hu h1
    · exact hw h2
  | .cons _ (.cons _ (.cons _ _)), hp => simp at hp

/-- The distance form of two separation. -/
def DistSep (G : SimpleGraph V) (cl : V → Set V) (X : Set V) : Prop :=
  ∀ u w, u ∉ X → w ∉ X → cl u ≠ cl w → (2 : ℕ∞) < G.edist u w

lemma distSep_of_twoSep {cl : V → Set V} {X : Set V}
    (h : ∀ u w (p : G.Walk u w), u ∉ X → w ∉ X → cl u ≠ cl w → HasTwoConsecutive p X) :
    DistSep G cl X := by
  intro u w hu hw hne
  by_contra hle
  push Not at hle
  obtain ⟨k, hk⟩ : ∃ k : ℕ, G.edist u w = k :=
    ENat.ne_top_iff_exists.1 (ne_top_of_le_ne_top (by decide) hle) |>.imp fun _ h => h.symm
  obtain ⟨p, hp⟩ := exists_walk_of_edist_eq_coe hk
  have : k ≤ 2 := by exact_mod_cast hk ▸ hle
  exact not_hasTwoConsecutive_of_length_le_two p X hu hw (hp ▸ this) (h u w p hu hw hne)

lemma twoSep_of_distSep {cl : V → Set V} {X : Set V} (h : DistSep G cl X) :
    ∀ u w (p : G.Walk u w), u ∉ X → w ∉ X → cl u ≠ cl w → HasTwoConsecutive p X := by
  -- invariant along a walk ending at a non-`X` node `w` without two consecutive `X` nodes
  have key : ∀ a w (p : G.Walk a w), w ∉ X → ¬ HasTwoConsecutive p X →
      (a ∉ X → cl a = cl w) ∧ (a ∈ X → ∀ b, G.Adj b a → b ∉ X → cl b = cl w) := by
    intro a w p hw
    induction p with
    | nil => exact fun _ => ⟨fun _ => rfl, fun ha => absurd ha hw⟩
    | @cons a a' w hadj p ih =>
      intro hno
      have hno' : ¬ HasTwoConsecutive p X := fun ⟨d, hd, h1, h2⟩ =>
        hno ⟨d, by simp [hd], h1, h2⟩
      obtain ⟨ih1, ih2⟩ := ih hw hno'
      have hd : ¬ (a ∈ X ∧ a' ∈ X) := fun ⟨h1, h2⟩ =>
        hno ⟨⟨(a, a'), hadj⟩, by simp, h1, h2⟩
      have close : ∀ b c, b ∉ X → c ∉ X → G.edist b c ≤ 2 → cl b = cl c := by
        intro b c hb hc hbc
        by_contra hne
        exact absurd (h b c hb hc hne) (not_lt.2 hbc)
      refine ⟨fun ha => ?_, fun ha b hb hbX => ?_⟩
      · by_cases ha' : a' ∈ X
        · exact ih2 ha' a hadj ha
        · rw [← ih1 ha']
          exact close a a' ha ha' ((edist_eq_one_iff_adj.2 hadj).le.trans (by norm_num))
      · have ha' : a' ∉ X := fun h' => hd ⟨ha, h'⟩
        rw [← ih1 ha']
        refine close b a' hbX ha' ?_
        calc G.edist b a' ≤ G.edist b a + G.edist a a' := SimpleGraph.edist_triangle
          _ = 1 + 1 := by rw [edist_eq_one_iff_adj.2 hb, edist_eq_one_iff_adj.2 hadj]
          _ = 2 := by norm_num
  intro u w p hu hw hne
  by_contra hno
  exact hne ((key u w p hw hno).1 hu)

/-- Two separation is equivalent to its distance form. -/
lemma twoSep_iff {cl : V → Set V} {X : Set V} :
    (∀ u w (p : G.Walk u w), u ∉ X → w ∉ X → cl u ≠ cl w → HasTwoConsecutive p X) ↔
      DistSep G cl X :=
  ⟨distSep_of_twoSep, twoSep_of_distSep⟩

end TwoSep

namespace TSPartition

variable {G : SimpleGraph V} {t : ℕ} {ε : ℝ} (ts : TSPartition G t ε)

lemma sep : DistSep G ts.cl ts.X := distSep_of_twoSep ts.twoSep

lemma cl_eq_iff {u v : V} : ts.cl u = ts.cl v ↔ u ∈ ts.cl v :=
  ⟨fun h => h ▸ ts.mem_cl u, ts.cl_eq u v⟩

lemma mem_cl_comm {u v : V} : u ∈ ts.cl v ↔ v ∈ ts.cl u := by
  rw [← cl_eq_iff, ← cl_eq_iff, eq_comm]

/-- Lemma 3.3: for every node `v` there is a cluster `C` with `B₁(v) ⊆ C ∪ X`. -/
lemma exists_ball_subset (v : V) :
    ∃ w, ∀ u, (u = v ∨ G.Adj v u) → u ∈ ts.cl w ∨ u ∈ ts.X := by
  by_cases h : ∃ w, (w = v ∨ G.Adj v w) ∧ w ∉ ts.X
  · obtain ⟨w, hw, hwX⟩ := h
    refine ⟨w, fun u hu => ?_⟩
    by_cases huX : u ∈ ts.X
    · exact Or.inr huX
    · left
      rw [← cl_eq_iff]
      by_contra hne
      have := ts.sep u w huX hwX hne
      have h2 : G.edist u w ≤ 2 := by
        calc G.edist u w ≤ G.edist u v + G.edist v w := SimpleGraph.edist_triangle
          _ ≤ 1 + 1 := by
            gcongr
            · rcases hu with rfl | hu
              · simp
              · rw [SimpleGraph.edist_comm, edist_eq_one_iff_adj.2 hu]
            · rcases hw with rfl | hw
              · simp
              · rw [edist_eq_one_iff_adj.2 hw]
          _ = 2 := by norm_num
      exact absurd this (not_lt.2 h2)
  · push Not at h
    exact ⟨v, fun u hu => Or.inr (h u hu)⟩

/-- `H_C`: the nodes having a non-`X` node of the cluster `C = cl w` in their closed
neighbourhood. -/
def H (w : V) : Set V := {u | ∃ y, (y = u ∨ G.Adj u y) ∧ y ∈ ts.cl w ∧ y ∉ ts.X}

/-- Lemma 3.4 (2): the sets `H_C` of distinct clusters are disjoint. -/
lemma hset_disjoint {w w' : V} (hne : ts.cl w ≠ ts.cl w') {u : V} (hu : u ∈ ts.H w)
    (hu' : u ∈ ts.H w') : False := by
  obtain ⟨y, hy, hyC, hyX⟩ := hu
  obtain ⟨y', hy', hyC', hyX'⟩ := hu'
  have hcl : ts.cl y ≠ ts.cl y' := by
    rw [ts.cl_eq y w hyC, ts.cl_eq y' w' hyC']; exact hne
  have := ts.sep y y' hyX hyX' hcl
  have h2 : G.edist y y' ≤ 2 := by
    calc G.edist y y' ≤ G.edist y u + G.edist u y' := SimpleGraph.edist_triangle
      _ ≤ 1 + 1 := by
        gcongr
        · rcases hy with rfl | hy
          · simp
          · rw [SimpleGraph.edist_comm, edist_eq_one_iff_adj.2 hy]
        · rcases hy' with rfl | hy'
          · simp
          · rw [edist_eq_one_iff_adj.2 hy']
      _ = 2 := by norm_num
  exact absurd this (not_lt.2 h2)

/-- Lemma 3.4 (1): a node whose closed neighbourhood is not inside `X` lies in some `H_C`. -/
lemma mem_H_of_not_subset {u : V} (h : ¬ ∀ y, (y = u ∨ G.Adj u y) → y ∈ ts.X) :
    ∃ w, u ∈ ts.H w := by
  push Not at h
  obtain ⟨y, hy, hyX⟩ := h
  exact ⟨y, y, hy, ts.mem_cl y, hyX⟩

/-- If `u ∈ H_C` then `B₁(u) ⊆ C ∪ X` (Lemma 3.3 for the cluster of `H_C`). -/
lemma ball_subset_of_mem_H {w u : V} (hu : u ∈ ts.H w) :
    ∀ y, (y = u ∨ G.Adj u y) → y ∈ ts.cl w ∨ y ∈ ts.X := by
  obtain ⟨w', hw'⟩ := ts.exists_ball_subset u
  obtain ⟨y₀, hy₀, hy₀C, hy₀X⟩ := hu
  have hcl : ts.cl w' = ts.cl w := by
    rcases hw' y₀ hy₀ with h | h
    · rw [← ts.cl_eq y₀ w' h, ts.cl_eq y₀ w hy₀C]
    · exact absurd h hy₀X
  intro y hy
  rw [← hcl]; exact hw' y hy

end TSPartition

/-! ### Cluster-degeneracy (Definition 3) and Lemma 3.1 -/

section Degenerate

variable (G : SimpleGraph V)

/-- Definition 3, for the ordered partition into the clusters `C_i = idx⁻¹ {i}`: in every cluster
at most an `ε`-fraction of the nodes are *close-to-boundary*, i.e. at distance `≤ 2` from a node
of a later cluster. -/
def ClusterDegenerate (idx : V → ℕ) (ε : ℝ) : Prop :=
  ∀ i, ({v | idx v = i ∧ ∃ u, i < idx u ∧ G.edist v u ≤ 2}.ncard : ℝ) ≤
    ε * {v | idx v = i}.ncard

/-- Every cluster `idx⁻¹ {i}` has weak diameter at most `t`. -/
def WeaklyBounded (idx : V → ℕ) (t : ℕ) : Prop :=
  ∀ a b, idx a = idx b → G.edist a b ≤ t

variable {G}

/-- Lemma 3.1: an ordered partition with `ε`-cluster-degeneracy and weak diameter `≤ t` yields a
`(t, ε)`-TS partition (with `X` the close-to-boundary nodes). -/
noncomputable def TSPartition.ofDegenerate {idx : V → ℕ} {t : ℕ} {ε : ℝ}
    (hdeg : ClusterDegenerate G idx ε) (hdiam : WeaklyBounded G idx t) : TSPartition G t ε where
  cl v := {u | idx u = idx v}
  mem_cl v := rfl
  cl_eq u v h := by
    ext w; simp only [Set.mem_ofPred_eq] at h ⊢; rw [h]
  X := {v | ∃ u, idx v < idx u ∧ G.edist v u ≤ 2}
  twoSep := by
    apply twoSep_of_distSep
    intro u w hu hw hne
    by_contra hle
    push Not at hle
    have hidx : idx u ≠ idx w := by
      intro h; apply hne; ext y; simp only [Set.mem_ofPred_eq, h]
    rcases lt_or_gt_of_ne hidx with h | h
    · exact hu ⟨w, h, hle⟩
    · exact hw ⟨u, h, by rwa [SimpleGraph.edist_comm]⟩
  diam v a ha b hb := hdiam a b (by simp only [Set.mem_ofPred_eq] at ha hb; rw [ha, hb])
  ratio v := by
    have : ({u | idx u = idx v} ∩ {v | ∃ u, idx v < idx u ∧ G.edist v u ≤ 2}) =
        {w | idx w = idx v ∧ ∃ u, idx v < idx u ∧ G.edist w u ≤ 2} := by
      ext w; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, u, h2, h3⟩; exact ⟨h1, u, h1 ▸ h2, h3⟩
      · rintro ⟨h1, u, h2, h3⟩; exact ⟨h1, u, h1 ▸ h2, h3⟩
    rw [this]; exact hdeg (idx v)

end Degenerate

/-! ### Certifying and outputting a TS partition (Definition 4) -/

/-- The local output of a node certifying a TS partition: a cluster map and a set of marked
nodes; only their values near the node's own cluster are meaningful (`TSOut.Correct`). -/
abbrev TSOut (V : Type*) := (V → Set V) × Set V

/-- The output `o` of node `v` is correct for `ts` (Definition 4 (1),(2)): `v` knows the cluster
`C_u` of every node `u` at distance `≤ 2` from its own cluster `C_v` (i.e. `Comp(v)`), and the
separating set inside each of these clusters. -/
def TSOut.Correct {G : SimpleGraph V} {t : ℕ} {ε : ℝ} (ts : TSPartition G t ε) (v : V)
    (o : TSOut V) : Prop :=
  ∀ u, (∃ w ∈ ts.cl v, G.edist w u ≤ 2) → o.1 u = ts.cl u ∧ ∀ y ∈ ts.cl u, (y ∈ o.2 ↔ y ∈ ts.X)

/-- Definition 4: an `R`-PLS that certifies and outputs a `(t, ε)`-TS partition on the graphs
of `𝒢`. `ver G ℓ v = none` means that `v` rejects; `some o` means that it accepts with output `o`.
Completeness: on graphs admitting a TS partition, all nodes accept the honest labels. Soundness:
if all nodes accept, there is a TS partition for which all outputs are correct. -/
structure TSCert (𝒢 : Set (SimpleGraph V)) (t : ℕ) (ε : ℝ) (R : ℕ) where
  prov : SimpleGraph V → V → Label
  ver : SimpleGraph V → (V → Label) → V → Option (TSOut V)
  isLocal : IsLocal (ι := Unit) R (fun G _ ℓ v => ver G ℓ v)
  complete : ∀ G ∈ 𝒢, Nonempty (TSPartition G t ε) → ∀ v, (ver G (prov G) v).isSome
  sound : ∀ G ∈ 𝒢, ∀ ℓ : V → Label, (∀ v, (ver G ℓ v).isSome) →
    ∃ ts : TSPartition G t ε, ∀ v o, ver G ℓ v = some o → o.Correct ts v

/-- The cost of a TS certification scheme is at most `c`. -/
def TSCert.CostLE {𝒢 : Set (SimpleGraph V)} {t : ℕ} {ε : ℝ} {R : ℕ} (S : TSCert 𝒢 t ε R)
    (c : ℕ) : Prop :=
  ∀ G ∈ 𝒢, ∀ v, (S.prov G v).length ≤ c

end PLSTradeoff
