import Papers.PODC2026.PLSTradeoff.Tradeoff
import Podc.Foundations.Combinatorics.SimpleGraph.Ball

/-!
# Sharing a string with `O(1)` bits per node (Lemma 5.6)

On a connected graph, the prover can make every node output the same string `S ∈ {0,1}^r` with
`O(1 + r/n)` bits per node and verification radius `2r + 1` (the paper: `4r + 2`), in such a way
that whenever all nodes accept, they all output the same string.

* **Lemma B.1** (`exists_clusterFam`): for `r ≥ 1` and a connected graph there is a family `𝒞` of
  pairwise non-adjacent node sets ("0-clusters"), each inducing a connected subgraph with exactly
  `s = min r n` nodes (hence of induced diameter `≤ s - 1 ≤ r - 1`), such that every node is
  within distance `r` of one of them. The proof is an extremal argument (add, around a node at
  distance `> r` from all clusters, a connected set of `s` nodes inside its `(r-1)`-ball) instead
  of the paper's iterative procedure; it is the same construction.
* The prover (`shareLabel`) marks the nodes of the clusters (bit `InU = 0`) and gives the node of
  rank `i` (by identifier) in its cluster `C` the `i`-th block of length `⌈r/|C|⌉` of `S`.
* The verifier (`shareVer`) of `v` works with *bounded* 0-clusters: `zball H Z r u` is the set of
  nodes reachable from `u` by a walk of length `≤ r` through marked nodes, and `dec` decodes the
  blocks stored on it. Node `v` checks that there is a marked node within distance `r`, and that
  all marked nodes within distance `r + 1` decode the same string; it outputs that string.
* Soundness (Lemmas B.2/B.3) is replaced by a direct argument: for adjacent `a, b`, the marked
  node chosen by `b` is within distance `r + 1` of `a`, so `a` checked that it decodes the same
  string as its own; by connectivity all nodes output the same string.

## Deviations from the paper

* The paper's verifier recognizes maximal 0-clusters inside `B_{4r+1}(v)` and checks their size.
  Using bounded clusters (`zball`), neither maximality nor size checks are needed for the
  property of Lemma 5.6 (agreement of all outputs), and radius `2r + 1` suffices; Lemmas B.2 and
  B.3 are not needed. The stated theorem keeps the paper's radius `4r + 2`
  (`exists_stringShare`); `exists_stringShare_sharp` has radius `2r + 1`.
* Lemma B.1 assumes `|V| > r`; for `n ≤ r` we use one cluster `V` of size `n` (this is what the
  construction gives with `s = min r n`), with `⌈r/n⌉` bits of `S` per node. The paper claims
  `O(1)` bits for every `r`, which is impossible when `n · O(1) < r` (counting); the cost here is
  `2⌈r/n⌉ + 6` (`= O(1)` when `n ≥ r`).
* `r = 0` is handled separately (every node outputs the empty string).
-/

namespace PLSTradeoff

open SimpleGraph
open Cslib.Local (GAgree loc mask loc_le gAgree_loc edist_le_edist_loc mask_of_le
  loc_edist_le_iff loc_adj_iff)

variable {V : Type*}

/-! ### Clusters inside a node set -/

section Clusters

-- CSLib candidate
/-- The subgraph of `H` induced on `Z`, as a graph on all of `V`. -/
def zG (H : SimpleGraph V) (Z : Set V) : SimpleGraph V where
  Adj x y := H.Adj x y ∧ x ∈ Z ∧ y ∈ Z
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => H.loopless.irrefl _ h.1⟩

lemma zG_le (H : SimpleGraph V) (Z : Set V) : zG H Z ≤ H := fun _ _ h => h.1

lemma zG_mono (H : SimpleGraph V) {Z Z' : Set V} (h : Z ⊆ Z') : zG H Z ≤ zG H Z' :=
  fun _ _ hxy => ⟨hxy.1, h hxy.2.1, h hxy.2.2⟩

/-- The bounded cluster of `u`: nodes reachable from `u` by a walk of length `≤ k` in `H[Z]`. -/
def zball (H : SimpleGraph V) (Z : Set V) (k : ℕ) (u : V) : Set V :=
  {w | (zG H Z).edist u w ≤ k}

/-- A walk starting in a set that is closed under adjacency stays in it. -/
lemma walk_mem_of_closed {H : SimpleGraph V} {C : Set V}
    (hC : ∀ a ∈ C, ∀ b, H.Adj a b → b ∈ C) :
    ∀ {x y : V} (p : H.Walk x y), x ∈ C → ∀ w ∈ p.support, w ∈ C
  | _, _, .nil, hx, w, hw => by
      rw [Walk.support_nil, List.mem_singleton] at hw
      exact hw ▸ hx
  | _, _, .cons h p, hx, w, hw => by
      rw [Walk.support_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact hx
      · exact walk_mem_of_closed hC p (hC _ hx _ h) w hw

-- CSLib candidate
/-- In a connected induced subgraph `H[C]`, distances are at most `|C| - 1`. -/
lemma zG_edist_le_ncard [Finite V] {H : SimpleGraph V} {C : Set V} {x y : V} (hx : x ∈ C)
    (h : (zG H C).Reachable x y) : (zG H C).edist x y ≤ (C.ncard - 1 : ℕ) := by
  classical
  obtain ⟨p⟩ := h
  have hp := p.bypass_isPath
  have hsub : ∀ w ∈ p.bypass.support, w ∈ C :=
    walk_mem_of_closed (H := zG H C) (fun _ _ _ hab => hab.2.2) p.bypass hx
  have hcard : p.bypass.support.toFinset.card ≤ C.ncard := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (fun w hw => hsub w (by simpa using hw))
  rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support] at hcard
  exact (edist_le p.bypass).trans (by exact_mod_cast (by omega))

/-- A family of 0-clusters: each has exactly `s` nodes and induced diameter `≤ r`, and distinct
clusters are not adjacent. -/
structure IsClusterFam (G : SimpleGraph V) (r s : ℕ) (𝒞 : Set (Set V)) : Prop where
  card : ∀ C ∈ 𝒞, C.ncard = s
  conn : ∀ C ∈ 𝒞, ∀ x ∈ C, ∀ y ∈ C, (zG G C).edist x y ≤ r
  sep : ∀ C ∈ 𝒞, ∀ C' ∈ 𝒞, C ≠ C' → ∀ x ∈ C, ∀ y ∈ C', ¬ G.Adj x y

/-- The bounded cluster (with respect to the union of the family) of a node of a cluster `C` is
`C` itself. -/
lemma IsClusterFam.zball_eq {G : SimpleGraph V} {r s : ℕ} {𝒞 : Set (Set V)}
    (h : IsClusterFam G r s 𝒞) {C : Set V} (hC : C ∈ 𝒞) {u : V} (hu : u ∈ C) :
    zball G (⋃₀ 𝒞) r u = C := by
  ext w
  constructor
  · intro hw
    have hw' : (zG G (⋃₀ 𝒞)).edist u w ≤ r := hw
    obtain ⟨p⟩ := edist_ne_top_iff_reachable.1 (ne_top_of_le_ne_top (ENat.natCast_ne_top r) hw')
    refine walk_mem_of_closed (fun a ha b hab => ?_) p hu w p.end_mem_support
    obtain ⟨C', hC', hb⟩ := Set.mem_sUnion.1 hab.2.2
    by_contra hbC
    exact h.sep C hC C' hC' (fun e => hbC (e ▸ hb)) a ha b hb hab.1
  · intro hw
    exact (edist_anti (zG_mono G (Set.subset_sUnion_of_mem hC))).trans (h.conn C hC u hu w hw)

-- CSLib candidate
/-- In a connected graph, every node lies in a set of exactly `k ≤ n` nodes inducing a connected
subgraph. -/
lemma exists_connSet [Fintype V] {G : SimpleGraph V} (hG : G.Connected) (v : V) {k : ℕ}
    (hk1 : 1 ≤ k) (hk : k ≤ Fintype.card V) :
    ∃ C : Set V, v ∈ C ∧ C.ncard = k ∧ ∀ x ∈ C, (zG G C).Reachable v x := by
  induction k, hk1 using Nat.le_induction with
  | base =>
    refine ⟨{v}, rfl, Set.ncard_singleton v, fun x hx => ?_⟩
    rw [Set.mem_singleton_iff.1 hx]
  | succ k hk1 ih =>
    obtain ⟨C, hvC, hCk, hCr⟩ := ih (by omega)
    obtain ⟨y, hy⟩ : ∃ y, y ∉ C := by
      by_contra hcon
      push Not at hcon
      have : C = Set.univ := Set.eq_univ_of_forall hcon
      rw [this, Set.ncard_univ, Nat.card_eq_fintype_card] at hCk
      omega
    obtain ⟨p⟩ := hG.preconnected v y
    obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart C hvC hy
    refine ⟨insert d.toProd.2 C, Set.mem_insert_of_mem _ hvC,
      by rw [Set.ncard_insert_of_notMem hd2, hCk], ?_⟩
    have hle : zG G C ≤ zG G (insert d.toProd.2 C) := zG_mono G (Set.subset_insert _ _)
    intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | hx
    · exact ((hCr _ hd1).mono hle).trans
        (Adj.reachable ⟨d.adj, Set.mem_insert_of_mem _ hd1, Set.mem_insert _ _⟩)
    · exact (hCr x hx).mono hle

/-- One step of the construction of Lemma B.1: around a node `v` at distance `> r` from all
clusters, a new cluster can be added. -/
lemma IsClusterFam.extend [Fintype V] {G : SimpleGraph V} (hG : G.Connected) {r : ℕ}
    (hr : 0 < r) {𝒞 : Set (Set V)} (h : IsClusterFam G r (min r (Fintype.card V)) 𝒞) {v : V}
    (hv : ∀ C ∈ 𝒞, ∀ u ∈ C, (r : ℕ∞) < G.edist v u) :
    ∃ 𝒞', IsClusterFam G r (min r (Fintype.card V)) 𝒞' ∧ (⋃₀ 𝒞).ncard < (⋃₀ 𝒞').ncard := by
  set s := min r (Fintype.card V) with hs
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
  obtain ⟨C, hvC, hCs, hCr⟩ := exists_connSet hG v (k := s) (by omega) (by omega)
  have hdiam : ∀ x ∈ C, ∀ y ∈ C, (zG G C).edist x y ≤ (s - 1 : ℕ) := by
    intro x hx y hy
    have := zG_edist_le_ncard hx ((hCr x hx).symm.trans (hCr y hy))
    rwa [hCs] at this
  have hnear : ∀ x ∈ C, G.edist v x ≤ (r - 1 : ℕ) := fun x hx =>
    (edist_anti (zG_le G C)).trans ((hdiam v hvC x hx).trans (by exact_mod_cast (by omega)))
  have hfar : ∀ C' ∈ 𝒞, ∀ x ∈ C, ∀ y ∈ C', ¬ G.Adj x y := by
    intro C' hC' x hx y hy hxy
    have h1 : G.edist v y ≤ (r - 1 + 1 : ℕ) :=
      edist_le_natCast_add (hnear x hx) ((edist_eq_one_iff_adj.2 hxy).le)
    rw [show r - 1 + 1 = r by omega] at h1
    exact absurd (hv C' hC' y hy) (not_lt.2 h1)
  refine ⟨insert C 𝒞, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro C' hC'
    rcases Set.mem_insert_iff.1 hC' with rfl | hC'
    · exact hCs
    · exact h.card C' hC'
  · intro C' hC' x hx y hy
    rcases Set.mem_insert_iff.1 hC' with rfl | hC'
    · exact (hdiam x hx y hy).trans (by exact_mod_cast (by omega))
    · exact h.conn C' hC' x hx y hy
  · intro C₁ h₁ C₂ h₂ hne x hx y hy
    rcases Set.mem_insert_iff.1 h₁ with e₁ | h₁ <;> rcases Set.mem_insert_iff.1 h₂ with e₂ | h₂
    · exact absurd (e₁.trans e₂.symm) hne
    · rw [e₁] at hx; exact hfar C₂ h₂ x hx y hy
    · rw [e₂] at hy; exact fun hxy => hfar C₁ h₁ y hy x hx hxy.symm
    · exact h.sep C₁ h₁ C₂ h₂ hne x hx y hy
  · refine Set.ncard_lt_ncard ⟨Set.sUnion_subset_sUnion (Set.subset_insert _ _), fun hsub => ?_⟩
    obtain ⟨C', hC', hvC'⟩ :=
      Set.mem_sUnion.1 (hsub (Set.mem_sUnion_of_mem hvC (Set.mem_insert _ _)))
    exact absurd (hv C' hC' v hvC') (by simp)

/-- **Lemma B.1** of [Filtser–Fischer, PODC 2026] (generalized to all `n`): in a connected graph,
for `r ≥ 1`, there is a family of pairwise non-adjacent 0-clusters, each inducing a connected
subgraph on exactly `min r n` nodes, such that every node is within distance `r` of a cluster.
(The paper assumes `n > r`, where `min r n = r`.) -/
theorem exists_clusterFam [Fintype V] {G : SimpleGraph V} (hG : G.Connected) {r : ℕ}
    (hr : 0 < r) :
    ∃ 𝒞 : Set (Set V), IsClusterFam G r (min r (Fintype.card V)) 𝒞 ∧
      ∀ v, ∃ C ∈ 𝒞, ∃ u ∈ C, G.edist v u ≤ r := by
  suffices H : ∀ m (𝒞 : Set (Set V)), IsClusterFam G r (min r (Fintype.card V)) 𝒞 →
      Fintype.card V - (⋃₀ 𝒞).ncard ≤ m → ∃ 𝒞' : Set (Set V),
        IsClusterFam G r (min r (Fintype.card V)) 𝒞' ∧ ∀ v, ∃ C ∈ 𝒞', ∃ u ∈ C, G.edist v u ≤ r by
    exact H _ ∅ ⟨by simp, by simp, by simp⟩ le_rfl
  intro m
  induction m with
  | zero =>
    intro 𝒞 h𝒞 hm
    refine ⟨𝒞, h𝒞, ?_⟩
    by_contra hv
    push Not at hv
    obtain ⟨v, hv⟩ := hv
    obtain ⟨𝒞', -, hlt⟩ := h𝒞.extend hG hr hv
    have : (⋃₀ 𝒞').ncard ≤ Fintype.card V := by
      rw [← Nat.card_eq_fintype_card, ← Set.ncard_univ]
      exact Set.ncard_le_ncard (Set.subset_univ _)
    omega
  | succ m ih =>
    intro 𝒞 h𝒞 hm
    by_cases hc : ∀ v, ∃ C ∈ 𝒞, ∃ u ∈ C, G.edist v u ≤ r
    · exact ⟨𝒞, h𝒞, hc⟩
    · push Not at hc
      obtain ⟨v, hv⟩ := hc
      obtain ⟨𝒞', h𝒞', hlt⟩ := h𝒞.extend hG hr hv
      exact ih 𝒞' h𝒞' (by omega)

end Clusters

/-! ### The scheme -/

section Scheme

variable [Fintype V] [LinearOrder V]

/-- The marked nodes (`InU = 0`, i.e. members of 0-clusters). -/
def zeroSet (ℓ : V → Label) : Set V := {w | (parse (ℓ w)).1 = [true]}

/-- `DecodeLex` on the bounded 0-cluster of `u`: the concatenation of the blocks stored on it,
in the order of identifiers. -/
noncomputable def dec (H : SimpleGraph V) (r : ℕ) (ℓ : V → Label) (u : V) : List Bool :=
  ((sortedL (zball H (zeroSet ℓ) r u)).map fun w => (parse (ℓ w)).2).flatten

/-- The checks of `v` on a (localized) view `(H, ℓ)`: there is a marked node within distance
`r`, and all marked nodes within distance `r + 1` decode the same string. -/
def ShareCheck (H : SimpleGraph V) (r : ℕ) (ℓ : V → Label) (v : V) : Prop :=
  (∃ u ∈ zeroSet ℓ, H.edist v u ≤ r) ∧
  ∀ u ∈ zeroSet ℓ, ∀ u' ∈ zeroSet ℓ, H.edist v u ≤ (r + 1 : ℕ) → H.edist v u' ≤ (r + 1 : ℕ) →
    dec H r ℓ u = dec H r ℓ u'

/-- The output of `v` on a view: the string decoded at a marked node within distance `r`, if the
checks pass; `none` (reject) otherwise. -/
noncomputable def shareOut (H : SimpleGraph V) (r : ℕ) (ℓ : V → Label) (v : V) :
    Option (List Bool) :=
  open Classical in
  if h : ShareCheck H r ℓ v then some (dec H r ℓ (Classical.choose h.1)) else none

/-- The verifier: `shareOut` on the radius-`(2r+1)` view. -/
noncomputable def shareVer (r : ℕ) (G : SimpleGraph V) (ℓ : V → Label) (v : V) :
    Option (List Bool) :=
  shareOut (loc G v (2 * r + 1)) r (mask G v (2 * r + 1) ℓ) v

/-- The honest labels for the marked set `Z`: the bit `InU = 0` and, on `Z`, the block of `S`
indexed by the rank of the node in its cluster. -/
noncomputable def shareLabel (G : SimpleGraph V) (Z : Set V) (r : ℕ) (S : List Bool) (v : V) :
    Label :=
  open Classical in
  encList [[decide (v ∈ Z)],
    if v ∈ Z then chunk S (S.length ⌈/⌉ (zball G Z r v).ncard) ((sortedL (zball G Z r v)).idxOf v)
    else []]

/-- The honest prover: the labels for the clusters of Lemma B.1. -/
noncomputable def shareProv (r : ℕ) (G : SimpleGraph V) (S : List Bool) (v : V) : Label :=
  open Classical in
  if h : G.Connected ∧ 0 < r then
    shareLabel G (⋃₀ Classical.choose (exists_clusterFam h.1 h.2)) r S v
  else []

/-! #### Locality -/

omit [Fintype V] [LinearOrder V] in
lemma mem_zeroSet_mask {G : SimpleGraph V} {v w : V} {R : ℕ} {ℓ : V → Label}
    (hw : G.edist v w ≤ R) : w ∈ zeroSet (mask G v R ℓ) ↔ w ∈ zeroSet ℓ := by
  simp only [zeroSet, Set.mem_ofPred_eq, mask_of_le hw]

omit [Fintype V] [LinearOrder V] in
lemma le_of_lt_natCast_succ {e : ℕ∞} {m : ℕ} (h : e < ((m + 1 : ℕ) : ℕ∞)) : e ≤ m := by
  rw [Nat.cast_add, Nat.cast_one] at h
  exact (ENat.lt_add_one_iff (ENat.natCast_ne_top m)).1 h

omit [Fintype V] [LinearOrder V] in
/-- The marked subgraph seen by `v` agrees with the true one around `u`. -/
lemma gagree_zG {G : SimpleGraph V} {ℓ : V → Label} {v u : V} {a L R : ℕ}
    (hu : G.edist v u ≤ a) (h : a + L ≤ R) :
    GAgree (zG G (zeroSet ℓ)) (zG (loc G v R) (zeroSet (mask G v R ℓ))) u L := by
  intro x hx y
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := by
    rcases Nat.eq_zero_or_pos L with rfl | hL
    · simp at hx
    · exact ⟨L - 1, by omega⟩
  have hux : G.edist u x ≤ L' :=
    le_of_lt_natCast_succ (lt_of_le_of_lt (edist_anti (zG_le G _)) hx)
  have hvx : G.edist v x ≤ (a + L' : ℕ) := edist_le_natCast_add hu hux
  have hxZ := mem_zeroSet_mask (ℓ := ℓ) (R := R) (hvx.trans (by exact_mod_cast (by omega)))
  have hadj : (loc G v R).Adj x y ↔ G.Adj x y := loc_adj_iff (a := a + L') hvx (by omega)
  have hyZ : G.Adj x y → (y ∈ zeroSet (mask G v R ℓ) ↔ y ∈ zeroSet ℓ) := fun hxy =>
    mem_zeroSet_mask (R := R) ((edist_le_natCast_add hvx ((edist_eq_one_iff_adj.2 hxy).le)).trans
      (by exact_mod_cast (by omega)))
  show G.Adj x y ∧ x ∈ _ ∧ y ∈ _ ↔ (loc G v R).Adj x y ∧ x ∈ _ ∧ y ∈ _
  rw [hadj, hxZ]
  constructor
  · rintro ⟨hxy, hx, hy⟩
    exact ⟨hxy, hx, (hyZ hxy).2 hy⟩
  · rintro ⟨hxy, hx, hy⟩
    exact ⟨hxy, hx, (hyZ hxy).1 hy⟩

omit [Fintype V] [LinearOrder V] in
lemma zball_loc {G : SimpleGraph V} {ℓ : V → Label} {v u : V} {a L R : ℕ}
    (hu : G.edist v u ≤ a) (h : a + L ≤ R) :
    zball (loc G v R) (zeroSet (mask G v R ℓ)) L u = zball G (zeroSet ℓ) L u := by
  ext w
  exact (gagree_zG hu h).edist_le_iff le_rfl

/-- `v` decodes correctly at nodes `u` with `d(v, u) + r ≤ R`. -/
lemma dec_loc {G : SimpleGraph V} {ℓ : V → Label} {v u : V} {a r R : ℕ}
    (hu : G.edist v u ≤ a) (h : a + r ≤ R) :
    dec (loc G v R) r (mask G v R ℓ) u = dec G r ℓ u := by
  unfold dec
  rw [zball_loc hu h]
  congr 1
  refine List.map_congr_left fun w hw => ?_
  have hw'' : w ∈ zball G (zeroSet ℓ) r u := mem_sortedL.1 hw
  have hw' : (zG G (zeroSet ℓ)).edist u w ≤ r := hw''
  have : G.edist v w ≤ R :=
    (edist_le_natCast_add hu ((edist_anti (zG_le G _)).trans hw')).trans (by exact_mod_cast h)
  rw [mask_of_le this]

/-- The checks on the localized view are the checks on the whole configuration. -/
lemma shareCheck_loc_iff {G : SimpleGraph V} {r : ℕ} {ℓ : V → Label} {v : V} :
    ShareCheck (loc G v (2 * r + 1)) r (mask G v (2 * r + 1) ℓ) v ↔ ShareCheck G r ℓ v := by
  have hv : G.edist v v ≤ (0 : ℕ) := by simp
  have hd : ∀ {m : ℕ} {w : V}, m ≤ r + 1 →
      ((loc G v (2 * r + 1)).edist v w ≤ m ↔ G.edist v w ≤ m) :=
    fun hm => loc_edist_le_iff hv (by omega : 0 + (r + 1) ≤ 2 * r + 1) hm
  have hZ : ∀ {w : V}, G.edist v w ≤ (r + 1 : ℕ) →
      (w ∈ zeroSet (mask G v (2 * r + 1) ℓ) ↔ w ∈ zeroSet ℓ) :=
    fun hw => mem_zeroSet_mask (hw.trans (by exact_mod_cast (by omega)))
  have hdec : ∀ {w : V}, G.edist v w ≤ (r + 1 : ℕ) →
      dec (loc G v (2 * r + 1)) r (mask G v (2 * r + 1) ℓ) w = dec G r ℓ w :=
    fun hw => dec_loc hw (by omega)
  have hrr : ((r : ℕ) : ℕ∞) ≤ ((r + 1 : ℕ) : ℕ∞) := by exact_mod_cast (by omega)
  unfold ShareCheck
  constructor
  · rintro ⟨⟨u, hu, hvu⟩, hc⟩
    have hvu' := (hd (m := r) (by omega)).1 hvu
    refine ⟨⟨u, (hZ (hvu'.trans hrr)).1 hu, hvu'⟩, fun u hu u' hu' h1 h2 => ?_⟩
    rw [← hdec h1, ← hdec h2]
    exact hc u ((hZ h1).2 hu) u' ((hZ h2).2 hu') ((hd le_rfl).2 h1) ((hd le_rfl).2 h2)
  · rintro ⟨⟨u, hu, hvu⟩, hc⟩
    refine ⟨⟨u, (hZ (hvu.trans hrr)).2 hu, (hd (m := r) (by omega)).2 hvu⟩,
      fun u hu u' hu' h1 h2 => ?_⟩
    have h1' := (hd le_rfl).1 h1
    have h2' := (hd le_rfl).1 h2
    rw [hdec h1', hdec h2']
    exact hc u ((hZ h1').1 hu) u' ((hZ h2').1 hu') h1' h2'

lemma shareVer_isLocal (r : ℕ) :
    IsLocal (ι := Unit) (2 * r + 1) (fun G _ ℓ v => shareVer (V := V) r G ℓ v) := by
  refine isLocal_iff.2 fun G I ℓ G' I' ℓ' v h => ?_
  simp only [shareVer]
  rw [viewEq_loc_eq h, (viewEq_mask_eq h).2]

lemma shareOut_of_check {H : SimpleGraph V} {r : ℕ} {ℓ : V → Label} {v : V}
    (h : ShareCheck H r ℓ v) :
    ∃ u ∈ zeroSet ℓ, H.edist v u ≤ r ∧ shareOut H r ℓ v = some (dec H r ℓ u) := by
  refine ⟨Classical.choose h.1, (Classical.choose_spec h.1).1, (Classical.choose_spec h.1).2, ?_⟩
  unfold shareOut
  rw [dite_eq_left h]

lemma check_of_isSome {H : SimpleGraph V} {r : ℕ} {ℓ : V → Label} {v : V}
    (h : (shareOut H r ℓ v).isSome) : ShareCheck H r ℓ v := by
  by_contra hc
  unfold shareOut at h
  rw [dite_eq_right hc] at h
  simp at h

/-! #### Completeness -/

lemma zeroSet_shareLabel {G : SimpleGraph V} {Z : Set V} {r : ℕ} {S : List Bool} :
    zeroSet (shareLabel G Z r S) = Z := by
  ext w
  simp [zeroSet, shareLabel]

/-- The blocks stored on a cluster decode to `S`. -/
lemma dec_shareLabel {G : SimpleGraph V} {r s : ℕ} {𝒞 : Set (Set V)} (h : IsClusterFam G r s 𝒞)
    {C : Set V} (hC : C ∈ 𝒞) {u : V} (hu : u ∈ C) (S : List Bool) :
    dec G r (shareLabel G (⋃₀ 𝒞) r S) u = S := by
  unfold dec
  rw [zeroSet_shareLabel, h.zball_eq hC hu]
  have hmap : (sortedL C).map (fun w => (parse (shareLabel G (⋃₀ 𝒞) r S w)).2) =
      (sortedL C).map (fun w => chunk S (S.length ⌈/⌉ C.ncard) ((sortedL C).idxOf w)) := by
    refine List.map_congr_left fun w hw => ?_
    have hwC := mem_sortedL.1 hw
    have hwZ : w ∈ ⋃₀ 𝒞 := Set.mem_sUnion_of_mem hwC hC
    simp [shareLabel, hwZ, h.zball_eq hC hwC]
  rw [hmap, map_idxOf_eq _ (nodup_sortedL C), length_sortedL,
    flatten_chunks _ ((Set.ncard_pos (Set.toFinite _)).2 ⟨u, hu⟩)]

lemma shareProv_eq {G : SimpleGraph V} (hG : G.Connected) {r : ℕ} (hr : 0 < r) (S : List Bool) :
    shareProv r G S = shareLabel G (⋃₀ Classical.choose (exists_clusterFam hG hr)) r S := by
  funext w
  unfold shareProv
  rw [dite_eq_left ⟨hG, hr⟩]

/-- Completeness: on a connected graph, all nodes output `S` under the honest labels. -/
lemma shareVer_complete {G : SimpleGraph V} (hG : G.Connected) {r : ℕ} (hr : 0 < r)
    (S : List Bool) (v : V) : shareVer r G (shareProv r G S) v = some S := by
  have hspec := Classical.choose_spec (exists_clusterFam hG hr)
  rw [shareProv_eq hG hr]
  set 𝒞 := Classical.choose (exists_clusterFam hG hr)
  obtain ⟨h𝒞, hcov⟩ := hspec
  set ℓ := shareLabel G (⋃₀ 𝒞) r S
  have hdecS : ∀ u ∈ zeroSet ℓ, dec G r ℓ u = S := by
    intro u hu
    rw [zeroSet_shareLabel] at hu
    obtain ⟨C, hC, huC⟩ := Set.mem_sUnion.1 hu
    exact dec_shareLabel h𝒞 hC huC S
  have hcheck : ShareCheck G r ℓ v := by
    obtain ⟨C, hC, u, hu, hvu⟩ := hcov v
    refine ⟨⟨u, ?_, hvu⟩, fun u hu u' hu' _ _ => ?_⟩
    · rw [zeroSet_shareLabel]; exact Set.mem_sUnion_of_mem hu hC
    · rw [hdecS u hu, hdecS u' hu']
  obtain ⟨u, hu, hvu, hout⟩ := shareOut_of_check (shareCheck_loc_iff.2 hcheck)
  have hvu' : G.edist v u ≤ r := edist_le_edist_loc.trans hvu
  unfold shareVer
  rw [hout, dec_loc hvu' (by omega),
    hdecS u ((mem_zeroSet_mask (hvu'.trans (by exact_mod_cast (by omega)))).1 hu)]

/-! #### Soundness -/

/-- Soundness: on a connected graph, if all nodes accept, they all output the same string. -/
lemma shareVer_sound {G : SimpleGraph V} (hG : G.Connected) {r : ℕ} (ℓ : V → Label)
    (hall : ∀ v, (shareVer r G ℓ v).isSome) : ∃ S', ∀ v, shareVer r G ℓ v = some S' := by
  have hc : ∀ v, ShareCheck G r ℓ v := fun v => shareCheck_loc_iff.1 (check_of_isSome (hall v))
  have hout : ∀ v, ∃ u ∈ zeroSet ℓ, G.edist v u ≤ r ∧
      shareVer r G ℓ v = some (dec G r ℓ u) := by
    intro v
    obtain ⟨u, hu, hvu, h⟩ := shareOut_of_check (check_of_isSome (hall v))
    have hvu' : G.edist v u ≤ r := edist_le_edist_loc.trans hvu
    refine ⟨u, (mem_zeroSet_mask (hvu'.trans (by exact_mod_cast (by omega)))).1 hu, hvu', ?_⟩
    unfold shareVer
    rw [h, dec_loc hvu' (by omega)]
  choose u0 hu0Z hu0d hu0v using hout
  have hadj : ∀ a b, G.Adj a b → dec G r ℓ (u0 a) = dec G r ℓ (u0 b) := by
    intro a b hab
    have h1 : G.edist a (u0 b) ≤ (1 + r : ℕ) :=
      edist_le_natCast_add ((edist_eq_one_iff_adj.2 hab).le) (hu0d b)
    exact (hc a).2 _ (hu0Z a) _ (hu0Z b) ((hu0d a).trans (by exact_mod_cast (by omega)))
      (h1.trans (by exact_mod_cast (by omega)))
  obtain ⟨v₀⟩ := hG.nonempty
  refine ⟨dec G r ℓ (u0 v₀), fun v => ?_⟩
  rw [hu0v v, (hG.preconnected v v₀).apply_eq_of_forall_adj hadj]

/-! #### Cost -/

omit [Fintype V] [LinearOrder V] in
lemma ceilDiv_min_le {r n : ℕ} (hr : 0 < r) : r ⌈/⌉ min r n ≤ r ⌈/⌉ n + 1 := by
  rcases le_total r n with h | h
  · rw [min_eq_left h]
    exact (Nat.ceilDiv_le_of_le_mul hr (le_of_eq (mul_one r).symm)).trans (by omega)
  · rw [min_eq_right h]
    omega

lemma shareProv_length {G : SimpleGraph V} {r : ℕ} {S : List Bool} (v : V) (hS : S.length = r) :
    (shareProv r G S v).length ≤ 2 * (r ⌈/⌉ Fintype.card V) + 6 := by
  by_cases h : G.Connected ∧ 0 < r
  · rw [shareProv_eq h.1 h.2]
    have hspec := Classical.choose_spec (exists_clusterFam h.1 h.2)
    set 𝒞 := Classical.choose (exists_clusterFam h.1 h.2)
    obtain ⟨h𝒞, -⟩ := hspec
    unfold shareLabel
    simp only [length_encList, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil]
    split_ifs with hv
    · obtain ⟨C, hC, hvC⟩ := Set.mem_sUnion.1 hv
      rw [h𝒞.zball_eq hC hvC, h𝒞.card C hC, hS]
      have := (length_chunk_le S (r ⌈/⌉ min r (Fintype.card V))
        ((sortedL C).idxOf v)).trans (ceilDiv_min_le h.2)
      omega
    · simp
  · unfold shareProv
    rw [dite_eq_right h]
    simp

end Scheme

/-! ### Lemma 5.6 -/

section Main

variable [Fintype V] [LinearOrder V]

/-- **Lemma 5.6** of [Filtser–Fischer, PODC 2026], sharp version: a `(2r+1)`-PLS on connected
graphs whose honest prover makes all nodes output `S ∈ {0,1}^r`, such that whenever all nodes
accept they all output the same string, with `2⌈r/n⌉ + 6` bits per node. -/
theorem exists_stringShare_sharp (r : ℕ) :
    ∃ (prov : SimpleGraph V → List Bool → V → Label)
      (ver : SimpleGraph V → (V → Label) → V → Option (List Bool)),
      IsLocal (ι := Unit) (2 * r + 1) (fun G _ ℓ v => ver G ℓ v) ∧
      (∀ G : SimpleGraph V, G.Connected → ∀ S : List Bool, S.length = r → ∀ v,
        ver G (prov G S) v = some S) ∧
      (∀ G : SimpleGraph V, G.Connected → ∀ ℓ : V → Label, (∀ v, (ver G ℓ v).isSome) →
        ∃ S', ∀ v, ver G ℓ v = some S') ∧
      (∀ G S v, S.length = r → (prov G S v).length ≤ 2 * (r ⌈/⌉ Fintype.card V) + 6) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨fun _ _ _ => [], fun _ _ _ => some [], fun _ _ _ _ _ _ => rfl,
      fun G _ S hS v => ?_, fun G _ ℓ _ => ⟨[], fun _ => rfl⟩, fun _ _ _ _ => by simp⟩
    rw [List.length_eq_zero_iff.1 hS]
  · exact ⟨shareProv r, shareVer r, shareVer_isLocal r,
      fun G hG S _ v => shareVer_complete hG hr S v,
      fun G hG ℓ h => shareVer_sound hG ℓ h, fun G S v hS => shareProv_length v hS⟩

/-- **Lemma 5.6** of [Filtser–Fischer, PODC 2026]: for every `r` there is a `(4r+2)`-PLS on
connected graphs such that, for every `S ∈ {0,1}^r`, under the honest labels all nodes output
`S`, and under any labeling either some node rejects (outputs `none`) or all nodes output the
same string `S'`. The cost is `2⌈r/n⌉ + 8 = O(1 + r/n)` bits per node (`O(1)` when `n ≥ r`; the
paper's `O(1)` for all `r` is impossible when `n < r/O(1)`). -/
theorem exists_stringShare (r : ℕ) :
    ∃ (prov : SimpleGraph V → List Bool → V → Label)
      (ver : SimpleGraph V → (V → Label) → V → Option (List Bool)),
      IsLocal (ι := Unit) (4 * r + 2) (fun G _ ℓ v => ver G ℓ v) ∧
      (∀ G : SimpleGraph V, G.Connected → ∀ S : List Bool, S.length = r → ∀ v,
        ver G (prov G S) v = some S) ∧
      (∀ G : SimpleGraph V, G.Connected → ∀ ℓ : V → Label, (∀ v, (ver G ℓ v).isSome) →
        ∃ S', ∀ v, ver G ℓ v = some S') ∧
      (∀ G S v, S.length = r → (prov G S v).length ≤ 2 * (r ⌈/⌉ Fintype.card V) + 8) := by
  obtain ⟨prov, ver, hloc, hc, hs, hcost⟩ := exists_stringShare_sharp (V := V) r
  exact ⟨prov, ver, hloc.mono (by omega), hc, hs,
    fun G S v hS => (hcost G S v hS).trans (by omega)⟩

end Main

end PLSTradeoff
