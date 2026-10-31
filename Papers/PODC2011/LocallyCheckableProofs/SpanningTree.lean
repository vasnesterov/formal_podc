import Papers.PODC2011.LocallyCheckableProofs.LocalTools

/-!
# The spanning-tree certificate of Korman–Kutten–Peleg (Section 5.1)

"Any spanning tree `T` can be equipped with a proof of size `O(log n)` that, for each vertex `v`,
consists of (i) the identity of a particular vertex `a`, the root, and (ii) the distance from `v` to
`a` in `T`." We also give every node a parent pointer (the identifier of its parent), which makes
the tree explicit; all three numbers are `O(log n)`-bit identifiers or distances.

`TreeOK G H rt d par v` is the radius-1 check at `v`: all `G`-neighbours agree on the root `rt`;
`d v = 0` iff `v` is the root; a non-root `v` has its parent `par v` among its `H`-neighbours
(`H ≤ G` is the graph of allowed tree edges: the whole graph, or the marked edges `I.S`) with
`d (par v) + 1 = d v`.

* `treeOK_sound`: on a connected instance, if all nodes accept then there is a root `r ∈ V`, all
  nodes know `r`, and every node `v` has an `H`-walk of length `d v` to `r` (following parents).
* `treeOK_complete`: if every node reaches `r ∈ V` in `H`, then the root `r`, the distances
  `H.dist · r < n` and suitable parents in `V` are accepted everywhere.
* `isAcyclic_of_treeEdges` / `treeEdges_complete`: with the extra check `TreeEdges` (every
  `H`-edge at `v` is a tree edge `{v, par v}` or `{u, par u}`), acceptance certifies that `H` is
  acyclic, and every acyclic connected `H` passes it.
* Counters along the tree (`childSum`, `count_root`, `count_le_root`, `exists_count`): if every
  node checks `cnt v = 1 + Σ_{children u} cnt u`, then `cnt root = n` (no acyclicity needed: each
  non-root node is the child of exactly one node), so every node can be convinced of `n`.
-/

namespace Podc.LocallyCheckableProofs

open SimpleGraph Finset

variable {L : Type*}

/-- The family of connected instances with identifiers in `{1, …, n^c}` (Section 5). -/
def connIdFamily (c : ℕ) : Set (Inst L) := {I | I.Conn ∧ I.IdBound c}

/-- The local check of the spanning-tree certificate at `v` (root `rt`, distance `d`, parent `par`;
tree edges taken from `H`). -/
def TreeOK (G H : SimpleGraph ℕ) (rt d par : ℕ → ℕ) (v : ℕ) : Prop :=
  (∀ u, G.Adj v u → rt u = rt v) ∧ (d v = 0 ↔ v = rt v) ∧
    (v ≠ rt v → H.Adj v (par v) ∧ d (par v) + 1 = d v)

/-- `TreeOK` only depends on the radius-one data of `v`. -/
lemma treeOK_congr {G H G' H' : SimpleGraph ℕ} {rt d par rt' d' par' : ℕ → ℕ} {v : ℕ}
    (hG : ∀ u, G.Adj v u ↔ G'.Adj v u) (hH : ∀ u, H.Adj v u ↔ H'.Adj v u) (hHG : H ≤ G)
    (hrt : ∀ u, G.Adj v u → rt u = rt' u) (hd : ∀ u, G.Adj v u → d u = d' u)
    (hrt0 : rt v = rt' v) (hd0 : d v = d' v) (hpar0 : par v = par' v) :
    TreeOK G H rt d par v ↔ TreeOK G' H' rt' d' par' v := by
  unfold TreeOK
  rw [← hrt0, ← hd0, ← hpar0]
  refine and_congr ⟨fun h u hu => ?_, fun h u hu => ?_⟩ (and_congr Iff.rfl (imp_congr_right
    fun _ => ⟨fun ⟨h1, h2⟩ => ⟨(hH _).1 h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨(hH _).2 h1, ?_⟩⟩))
  · rw [← hrt u ((hG u).2 hu)]; exact h u ((hG u).2 hu)
  · rw [hrt u hu]; exact h u ((hG u).1 hu)
  · rw [← hd _ (hHG h1)]; exact h2
  · rw [hd _ (hHG ((hH _).2 h1))]; exact h2

/-- The tree check on fields `i, j, k` (root, distance, parent) only depends on the radius-1
data. -/
lemma Nbr1Eq.treeOK {I I' : Inst L} {Q Q' : ℕ → List ℕ} {v : ℕ} (h : Nbr1Eq I Q I' Q' v)
    {H H' : SimpleGraph ℕ} (hH : ∀ u, H.Adj v u ↔ H'.Adj v u) (hHG : H ≤ I.G) (i j k : ℕ) :
    TreeOK I.G H (natField i Q) (natField j Q) (natField k Q) v ↔
      TreeOK I'.G H' (natField i Q') (natField j Q') (natField k Q') v :=
  treeOK_congr h.adj hH hHG (h.field i).1 (h.field j).1 (h.field i).2 (h.field j).2
    (h.field k).2

/-- A quantity that all neighbours agree on is constant along walks. -/
lemma const_of_walk {I : Inst L} {f : ℕ → ℕ} (hf : ∀ v ∈ I.V, ∀ u, I.G.Adj v u → f u = f v)
    {a b : ℕ} (p : I.G.Walk a b) (ha : a ∈ I.V) : f b = f a := by
  induction p with
  | nil => rfl
  | cons h q ih => rw [ih (I.sub' h), hf _ ha _ h]

/-- A quantity that all neighbours agree on is constant on a connected instance. -/
lemma const_of_conn {I : Inst L} (hc : I.Conn) {f : ℕ → ℕ}
    (hf : ∀ v ∈ I.V, ∀ u, I.G.Adj v u → f u = f v) {a b : ℕ} (ha : a ∈ I.V) (hb : b ∈ I.V) :
    f b = f a :=
  const_of_walk hf (hc.2 a ha b hb).some ha

/-- Following parents from a node with `d v = k` reaches the root in `k` steps. -/
lemma treeOK_walk {I : Inst L} {H : SimpleGraph ℕ} (hH : H ≤ I.G) {rt d par : ℕ → ℕ} {r : ℕ}
    (h : ∀ v ∈ I.V, TreeOK I.G H rt d par v) (hrt : ∀ v ∈ I.V, rt v = r) :
    ∀ v ∈ I.V, ∃ p : H.Walk v r, p.length = d v := by
  intro v hv
  induction hk : d v generalizing v with
  | zero =>
    have : v = r := by rw [← hrt v hv]; exact (h v hv).2.1.1 hk
    subst this; exact ⟨Walk.nil, rfl⟩
  | succ k ih =>
    have hne : v ≠ rt v := fun he => by have := (h v hv).2.1.2 he; omega
    obtain ⟨hadj, hdp⟩ := (h v hv).2.2 hne
    obtain ⟨p, hp⟩ := ih (par v) (I.sub' (hH hadj)) (by omega)
    exact ⟨Walk.cons hadj p, by simp [hp]⟩

/-- **Soundness of the spanning-tree certificate.** On a connected instance, if every node
accepts, there is a root `r ∈ V` known to all nodes, and every node `v` reaches `r` by an
`H`-walk of length `d v` (along the parent pointers). -/
theorem treeOK_sound {I : Inst L} (hc : I.Conn) {H : SimpleGraph ℕ} (hH : H ≤ I.G)
    {rt d par : ℕ → ℕ} (h : ∀ v ∈ I.V, TreeOK I.G H rt d par v) :
    ∃ r ∈ I.V, (∀ v ∈ I.V, rt v = r) ∧ ∀ v ∈ I.V, ∃ p : H.Walk v r, p.length = d v := by
  obtain ⟨v₀, hv₀⟩ := hc.1
  have hrt : ∀ v ∈ I.V, rt v = rt v₀ :=
    fun v hv => const_of_conn hc (fun w hw u hu => (h w hw).1 u hu) hv₀ hv
  obtain ⟨p, -⟩ := treeOK_walk hH h hrt v₀ hv₀
  exact ⟨rt v₀, Inst.support_subset hH p hv₀ _ p.end_mem_support, hrt,
    treeOK_walk hH h hrt⟩

/-- Distances inside an instance are smaller than the number of nodes. -/
lemma dist_lt_n {I : Inst L} {H : SimpleGraph ℕ} (hH : H ≤ I.G) {v r : ℕ} (hv : v ∈ I.V)
    (hvr : H.Reachable v r) : H.dist v r < I.n := by
  classical
  obtain ⟨p, hp, hlen⟩ := hvr.exists_path_of_dist
  have hsub : p.support.toFinset ⊆ I.V := fun x hx =>
    Inst.support_subset hH p hv x (List.mem_toFinset.1 hx)
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support] at this
  unfold Inst.n; omega

/-- A node at positive distance has a neighbour one step closer. -/
lemma exists_adj_dist {H : SimpleGraph ℕ} {v r : ℕ} (hvr : H.Reachable v r) (hne : v ≠ r) :
    ∃ u, H.Adj v u ∧ H.dist u r + 1 = H.dist v r := by
  obtain ⟨p, hp⟩ := hvr.exists_walk_length_eq_dist
  cases p with
  | nil => exact absurd rfl hne
  | @cons _ u _ hadj q =>
    refine ⟨u, hadj, ?_⟩
    have h1 : H.dist u r ≤ q.length := dist_le q
    have h2 : H.dist v r ≤ H.dist v u + H.dist u r :=
      (Walk.cons hadj Walk.nil : H.Walk v u).reachable.dist_triangle_left r
    rw [dist_eq_one_iff_adj.2 hadj] at h2
    simp at hp; omega

/-- **Completeness of the spanning-tree certificate.** If every node reaches `r ∈ V` in `H`, the
certificate with root `r`, distances `H.dist · r` and suitable parents is accepted everywhere;
distances are `< n` and parents are nodes. -/
theorem treeOK_complete {I : Inst L} {H : SimpleGraph ℕ} (hH : H ≤ I.G) {r : ℕ}
    (hreach : ∀ v ∈ I.V, H.Reachable v r) :
    ∃ par : ℕ → ℕ, ∀ v ∈ I.V,
      TreeOK I.G H (fun _ => r) (fun u => H.dist u r) par v ∧ H.dist v r < I.n ∧ par v ∈ I.V := by
  classical
  let par : ℕ → ℕ := fun v =>
    if h : ∃ u, H.Adj v u ∧ H.dist u r + 1 = H.dist v r then h.choose else v
  refine ⟨par, fun v hv => ⟨⟨fun _ _ => rfl, ?_, fun hne => ?_⟩, dist_lt_n hH hv (hreach v hv), ?_⟩⟩
  · simp only
    rw [dist_eq_zero_iff_eq_or_not_reachable]
    exact ⟨fun h => h.resolve_right (not_not.2 (hreach v hv)), Or.inl⟩
  · have hex := exists_adj_dist (hreach v hv) hne
    simp only [par, hex, ↓reduceDIte]
    exact hex.choose_spec
  · by_cases hex : ∃ u, H.Adj v u ∧ H.dist u r + 1 = H.dist v r
    · simp only [par, hex, ↓reduceDIte]; exact I.sub' (hH hex.choose_spec.1)
    · simp only [par, hex, ↓reduceDIte]; exact hv

/-! ### Certifying that `H` is acyclic -/

/-- Every `H`-edge at `v` is a tree edge. -/
def TreeEdges (H : SimpleGraph ℕ) (rt par : ℕ → ℕ) (v : ℕ) : Prop :=
  ∀ u, H.Adj v u → (v ≠ rt v ∧ u = par v) ∨ (u ≠ rt u ∧ par u = v)

lemma treeEdges_congr {H H' : SimpleGraph ℕ} {rt par rt' par' : ℕ → ℕ} {v : ℕ}
    (hH : ∀ u, H.Adj v u ↔ H'.Adj v u) (hrt : ∀ u, H.Adj v u → rt u = rt' u)
    (hpar : ∀ u, H.Adj v u → par u = par' u) (hrt0 : rt v = rt' v) (hpar0 : par v = par' v) :
    TreeEdges H rt par v ↔ TreeEdges H' rt' par' v := by
  unfold TreeEdges
  refine forall_congr' fun u => ⟨fun h hu => ?_, fun h hu => ?_⟩
  · have hu' := (hH u).2 hu
    rw [← hrt0, ← hpar0, ← hrt u hu', ← hpar u hu']; exact h hu'
  · rw [hrt0, hpar0, hrt u hu, hpar u hu]; exact h ((hH u).1 hu)

/-- Nodes whose parent chain reaches `x` before the root. -/
inductive Desc (par : ℕ → ℕ) (r x : ℕ) : ℕ → Prop
  | self : Desc par r x x
  | step {z : ℕ} : z ≠ r → Desc par r x (par z) → Desc par r x z

/-- **Acyclicity from the tree certificate.** If all nodes pass `TreeOK` and `TreeEdges` (with a
common root `r`), then `H` is acyclic. -/
theorem isAcyclic_of_treeEdges {I : Inst L} {H : SimpleGraph ℕ} (hH : H ≤ I.G) {r : ℕ}
    {rt d par : ℕ → ℕ} (hrt : ∀ v ∈ I.V, rt v = r) (htree : ∀ v ∈ I.V, TreeOK I.G H rt d par v)
    (hedges : ∀ v ∈ I.V, TreeEdges H rt par v) : H.IsAcyclic := by
  have hpar : ∀ z ∈ I.V, z ≠ r → H.Adj z (par z) ∧ d (par z) + 1 = d z := fun z hz hzr =>
    (htree z hz).2.2 (by rw [hrt z hz]; exact hzr)
  have desc_lt : ∀ x z, Desc par r x z → z ∈ I.V → z = x ∨ d x < d z := by
    intro x z hD
    induction hD with
    | self => exact fun _ => Or.inl rfl
    | @step z hzr _ ih =>
      intro hz
      obtain ⟨hadj, hd⟩ := hpar z hz hzr
      rcases ih (I.sub' (hH hadj)) with h | h
      · right; rw [← h]; omega
      · right; omega
  -- removing the edge `{x, par x}` disconnects `x` from `par x`
  have key : ∀ x ∈ I.V, x ≠ r →
      ¬ (H.deleteEdges {s(x, par x)}).Reachable x (par x) := by
    intro x hx hxr ⟨p⟩
    have closed : ∀ a b (q : (H.deleteEdges {s(x, par x)}).Walk a b), a ∈ I.V →
        Desc par r x a → Desc par r x b := by
      intro a b q
      induction q with
      | nil => exact fun _ h => h
      | @cons a c b hac q ih =>
        intro ha hD
        simp only [deleteEdges_adj, Set.mem_singleton_iff] at hac
        obtain ⟨hac, hne⟩ := hac
        have hc : c ∈ I.V := I.sub' (hH hac)
        apply ih hc
        rcases hedges a ha c hac with ⟨har, rfl⟩ | ⟨hcr, rfl⟩
        · cases hD with
          | self => exact (hne rfl).elim
          | step _ h => exact h
        · exact Desc.step (by rwa [hrt c hc] at hcr) hD
    have hD := closed x (par x) p hx Desc.self
    obtain ⟨hadj, hd⟩ := hpar x hx hxr
    rcases desc_lt x (par x) hD (I.sub' (hH hadj)) with h | h
    · exact hadj.ne h.symm
    · omega
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro v w hvw
  have hv : v ∈ I.V := I.sub (hH hvw)
  rw [isBridge_iff]
  rcases hedges v hv w hvw with ⟨hvr, rfl⟩ | ⟨hwr, hpw⟩
  · exact key v hv (by rwa [hrt v hv] at hvr)
  · have hw : w ∈ I.V := I.sub' (hH hvw)
    subst hpw
    rw [Sym2.eq_swap]
    exact fun h => key w hw (by rwa [hrt w hw] at hwr) h.symm

/-- On a shortest walk to `r`, every other node is strictly closer to `r`. -/
lemma dist_lt_of_mem_support {H : SimpleGraph ℕ} {u r x : ℕ} (p : H.Walk u r)
    (hp : p.length = H.dist u r) (hx : x ∈ p.support) (hxu : x ≠ u) : H.dist x r < H.dist u r := by
  classical
  have hspec := congrArg Walk.length (p.take_spec hx)
  rw [Walk.length_append] at hspec
  have h1 : H.dist x r ≤ (p.dropUntil x hx).length := dist_le _
  have h2 : (p.takeUntil x hx).length ≠ 0 := fun h0 => hxu (Walk.eq_of_length_eq_zero h0).symm
  omega

/-- In an acyclic graph, the neighbour of `v` one step closer to `r` is unique. -/
lemma eq_of_adj_dist {H : SimpleGraph ℕ} (hac : H.IsAcyclic) {v u u' r : ℕ} (hu : H.Adj v u)
    (hu' : H.Adj v u') (hdu : H.dist u r + 1 = H.dist v r) (hdu' : H.dist u' r + 1 = H.dist v r) :
    u = u' := by
  have hvr : H.Reachable v r := Reachable.of_dist_ne_zero (by omega)
  obtain ⟨p, hp⟩ := (hu.symm.reachable.trans hvr).exists_walk_length_eq_dist
  obtain ⟨p', hp'⟩ := (hu'.symm.reachable.trans hvr).exists_walk_length_eq_dist
  have hW := (Walk.cons hu p).isPath_of_length_eq_dist (by simp [hp, hdu])
  have hW' := (Walk.cons hu' p').isPath_of_length_eq_dist (by simp [hp', hdu'])
  have := congrArg (fun P : H.Path v r => P.1.snd) ((hac.subsingleton_path v r).elim ⟨_, hW⟩ ⟨_, hW'⟩)
  simpa using this

/-- **Completeness of the acyclicity check.** If `H` is acyclic and the parents are one step closer
to the root, then every `H`-edge is a tree edge. -/
theorem treeEdges_complete {I : Inst L} {H : SimpleGraph ℕ} (hH : H ≤ I.G) (hac : H.IsAcyclic)
    {r : ℕ} (hreach : ∀ v ∈ I.V, H.Reachable v r) {par : ℕ → ℕ}
    (hpar : ∀ v ∈ I.V, v ≠ r → H.Adj v (par v) ∧ H.dist (par v) r + 1 = H.dist v r) :
    ∀ v ∈ I.V, TreeEdges H (fun _ => r) par v := by
  intro v hv u hvu
  have hu : u ∈ I.V := I.sub' (hH hvu)
  have h1 : H.dist v r ≤ H.dist u r + 1 := by
    have := hvu.reachable.dist_triangle_left r
    rw [dist_eq_one_iff_adj.2 hvu] at this; omega
  have h2 : H.dist u r ≤ H.dist v r + 1 := by
    have := hvu.symm.reachable.dist_triangle_left r
    rw [dist_eq_one_iff_adj.2 hvu.symm] at this; omega
  have hne : H.dist u r ≠ H.dist v r := by
    intro heq
    obtain ⟨p, hp⟩ := (hreach u hu).exists_walk_length_eq_dist
    obtain ⟨q, hq⟩ := (hreach v hv).exists_walk_length_eq_dist
    by_cases hvp : v ∈ p.support
    · have := dist_lt_of_mem_support p hp hvp hvu.ne; omega
    · have hW : (Walk.cons hvu p).IsPath :=
        (Walk.cons_isPath_iff _ _).2 ⟨p.isPath_of_length_eq_dist hp, hvp⟩
      have := congrArg (fun P : H.Path v r => P.1.length)
        ((hac.subsingleton_path v r).elim ⟨_, hW⟩ ⟨_, q.isPath_of_length_eq_dist hq⟩)
      simp at this; omega
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hvr : v ≠ r := by rintro rfl; simp at hlt
    exact Or.inl ⟨hvr, eq_of_adj_dist hac hvu (hpar v hv hvr).1 (by omega) (hpar v hv hvr).2⟩
  · have hur : u ≠ r := by rintro rfl; simp at hlt
    exact Or.inr ⟨hur, eq_of_adj_dist hac (hpar u hu hur).1 hvu.symm (hpar u hu hur).2 (by omega)⟩

/-! ### Counters along the tree: every node learns `n` -/

open Classical in
/-- The sum of the counters of the children of `v`: neighbours `u` that are not the root and
whose parent is `v`. -/
noncomputable def childSum (I : Inst L) (rt par cnt : ℕ → ℕ) (v : ℕ) : ℕ :=
  ∑ u ∈ (I.nbrs v).filter (fun u => u ≠ rt u ∧ par u = v), cnt u

lemma childSum_congr {I I' : Inst L} {rt par cnt rt' par' cnt' : ℕ → ℕ} {v : ℕ}
    (hn : I.nbrs v = I'.nbrs v)
    (hf : ∀ u ∈ I.nbrs v, rt u = rt' u ∧ par u = par' u ∧ cnt u = cnt' u) :
    childSum I rt par cnt v = childSum I' rt' par' cnt' v := by
  unfold childSum
  rw [← hn]
  exact Finset.sum_congr (Finset.filter_congr fun u hu => by rw [(hf u hu).1, (hf u hu).2.1])
    fun u hu => (hf u (Finset.mem_filter.1 hu).1).2.2

lemma childSum_congr_cnt {I : Inst L} {rt par cnt cnt' : ℕ → ℕ} {v : ℕ}
    (h : ∀ u ∈ I.nbrs v, u ≠ rt u → par u = v → cnt u = cnt' u) :
    childSum I rt par cnt v = childSum I rt par cnt' v := by
  unfold childSum
  exact Finset.sum_congr rfl fun u hu => by
    obtain ⟨hu, h1, h2⟩ := Finset.mem_filter.1 hu; exact h u hu h1 h2

lemma childSum_eq {I : Inst L} {r : ℕ} {rt par cnt : ℕ → ℕ} (hrt : ∀ v ∈ I.V, rt v = r)
    (v : ℕ) [DecidablePred fun u => I.G.Adj v u ∧ u ≠ r ∧ par u = v] :
    childSum I rt par cnt v =
      ∑ u ∈ I.V, if I.G.Adj v u ∧ u ≠ r ∧ par u = v then cnt u else 0 := by
  classical
  rw [← Finset.sum_filter, childSum, Inst.nbrs, Finset.filter_filter]
  refine Finset.sum_congr (Finset.filter_congr fun u hu => ?_) fun _ _ => rfl
  rw [hrt u hu]

/-- **Counting along the tree.** If all non-root nodes point to a neighbouring parent and every
node checks `cnt v = 1 + Σ_{children} cnt`, then the root's counter is `n`. (No acyclicity is
needed: summing the checks counts every non-root node exactly once as a child.) -/
theorem count_root {I : Inst L} {r : ℕ} (hr : r ∈ I.V) {rt par cnt : ℕ → ℕ}
    (hrt : ∀ v ∈ I.V, rt v = r) (hpar : ∀ u ∈ I.V, u ≠ r → I.G.Adj u (par u))
    (hcnt : ∀ v ∈ I.V, cnt v = 1 + childSum I rt par cnt v) : cnt r = I.n := by
  classical
  have hsum : ∑ v ∈ I.V, childSum I rt par cnt v = ∑ u ∈ I.V.erase r, cnt u := by
    rw [Finset.sum_congr rfl fun v _ => childSum_eq hrt v, Finset.sum_comm,
      ← Finset.filter_ne' I.V r, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u hu => ?_
    by_cases hur : u = r
    · simp [hur]
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hur)]
      rw [Finset.sum_congr rfl fun v _ => (show (if I.G.Adj v u ∧ u ≠ r ∧ par u = v then cnt u
          else 0) = if par u = v then cnt u else 0 by
        by_cases hv : par u = v
        · subst hv; simp [(hpar u hu hur).symm, hur]
        · simp [hv])]
      rw [Finset.sum_ite_eq]
      simp [I.sub' (hpar u hu hur)]
  have h1 : ∑ v ∈ I.V, cnt v = I.n + ∑ u ∈ I.V.erase r, cnt u := by
    rw [Finset.sum_congr rfl hcnt, Finset.sum_add_distrib, hsum]; simp [Inst.n]
  have h2 := Finset.add_sum_erase I.V cnt hr
  omega

/-- The counters are at most the root's counter. -/
theorem count_le_root {I : Inst L} {r : ℕ} {rt d par cnt : ℕ → ℕ}
    (hrt : ∀ v ∈ I.V, rt v = r)
    (htree : ∀ v ∈ I.V, v ≠ r → I.G.Adj v (par v) ∧ d (par v) + 1 = d v)
    (hcnt : ∀ v ∈ I.V, cnt v = 1 + childSum I rt par cnt v) : ∀ v ∈ I.V, cnt v ≤ cnt r := by
  intro v hv
  induction hk : d v generalizing v with
  | zero =>
    by_cases hvr : v = r
    · rw [hvr]
    · have := (htree v hv hvr).2; omega
  | succ k ih =>
    by_cases hvr : v = r
    · rw [hvr]
    obtain ⟨hadj, hd⟩ := htree v hv hvr
    have hp : par v ∈ I.V := I.sub' hadj
    refine le_trans ?_ (ih (par v) hp (by omega))
    rw [hcnt (par v) hp]
    have : cnt v ≤ childSum I rt par cnt (par v) := by
      classical
      unfold childSum
      refine Finset.single_le_sum (f := cnt) (fun _ _ => Nat.zero_le _) ?_
      refine Finset.mem_filter.2 ⟨Inst.mem_nbrs.2 hadj.symm, ?_, rfl⟩
      rw [hrt v hv]; exact hvr
    omega

/-- Counters by fuel: `cntFuel k v` is the number of descendants of `v` within `k - 1` levels. -/
noncomputable def cntFuel (I : Inst L) (rt par : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0 => fun _ => 1
  | k + 1 => fun v => 1 + childSum I rt par (cntFuel I rt par k) v

/-- **Completeness of the counters.** Along a tree with depths `d < n`, counters satisfying all
local checks exist. -/
theorem exists_count {I : Inst L} {r : ℕ} {rt d par : ℕ → ℕ} (hrt : ∀ v ∈ I.V, rt v = r)
    (htree : ∀ u ∈ I.V, u ≠ r → d (par u) + 1 = d u) (hdn : ∀ v ∈ I.V, d v < I.n) :
    ∃ cnt : ℕ → ℕ, ∀ v ∈ I.V, cnt v = 1 + childSum I rt par cnt v := by
  refine ⟨fun v => cntFuel I rt par (I.n - d v) v, fun v hv => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, I.n - d v = k + 1 := ⟨I.n - d v - 1, by have := hdn v hv; omega⟩
  simp only [hk, cntFuel]
  congr 1
  refine childSum_congr_cnt fun u hu hur hpu => ?_
  have hu' : u ∈ I.V := I.sub' (Inst.mem_nbrs.1 hu)
  have := htree u hu' (by rwa [hrt u hu'] at hur)
  rw [hpu] at this
  rw [show I.n - d u = k by omega]

end Podc.LocallyCheckableProofs
