import Papers.PODC2011.UniformLocalAlgorithms.Model

/-!
# Pruning algorithms for ruling sets and maximal matching (Section 3.2)

A. Korman, J.-S. Sereni, L. Viennot, *Toward More Localized Local Algorithms: Removing
Assumptions Concerning Global Knowledge*, PODC 2011 / Distributed Computing (arXiv:1512.03306).

* `allFinite`: the family of all (normalized) finite instances; the parameters `numNodes` (`n`)
  and `maxDeg` (`Δ`); `NonDecreasing F p` (Section 2) and the proofs that `n` and `Δ` are
  non-decreasing (`numNodes_nonDecreasing`, `maxDeg_nonDecreasing`).
* `observation_3_1_2`: a pruning algorithm that does not change the inputs of the non-pruned nodes
  is monotone with respect to every non-decreasing parameter.
* `rulingSet β`: the `(2, β)`-ruling set problem (`MIS = rulingSet 1`); `rulingPruning β`: the
  pruning algorithm `P_(2,β)`; `observation_3_2`: it is a pruning algorithm running in `β + 1`
  rounds, monotone w.r.t. `n` and `Δ` (we need `1 ≤ β`; for `β = 0` gluing fails).
* `mmPaper`: maximal matching with the paper's encoding (two neighbours are matched iff they have
  the same output and no other neighbour of either has this output); `mmPaperW`: the set of nodes
  pruned by the paper's `P_MM`. `observation_3_3_false`: **Observation 3.3 is false**: no pruning
  algorithm for `mmPaper` prunes exactly the paper's set `W` (gluing fails on a path with 4 nodes).
* `mmId`: maximal matching encoded by partner identities; `mmPruning`: the analogous pruning rule;
  `observation_3_3_repaired`: it is a pruning algorithm running in 2 rounds, monotone w.r.t. `n`
  and `Δ`.
-/

open Cslib.Local SimpleGraph

namespace Podc.UniformLocalAlgorithms

variable {V α β : Type*}

/-! ### Sub-instances, the family of finite instances, parameters -/

/-- `(G', x') ⊆ (G, x)`: the nodes of `x'` are nodes of `x` with the same inputs, and the graph of
`(G', x')` is a subgraph of the graph of `(G, x)`. -/
def SubInst (G' : SimpleGraph V) (x' : V → Option α) (G : SimpleGraph V) (x : V → Option α) :
    Prop :=
  (∀ v, (x' v).isSome → (x v).isSome) ∧ (∀ v, (x' v).isSome → x' v = x v) ∧ res G' x' ≤ res G x

/-- The family of all finite instances (normalized: the graph is induced by the node set). -/
def allFinite : Family V α where
  mem G x := res G x = G ∧ (supp x).Finite
  res_eq h := h.1

/-- The number of nodes `n` of an instance. -/
noncomputable def numNodes : Param V α := fun _ x => (supp x).ncard

/-- The maximum degree `Δ` of an instance: the largest degree in `res G x` of a node of the
instance (`0` for the empty instance). -/
noncomputable def maxDeg : Param V α :=
  fun G x => sSup ((fun v => ((res G x).neighborSet v).ncard) '' supp x)

/-- A parameter is non-decreasing (Section 2) if `p(G', x') ≤ p(G, x)` whenever `(G', x') ∈ F`
and `(G', x') ⊆ (G, x) ∈ F`. -/
def NonDecreasing (F : Family V α) (p : Param V α) : Prop :=
  ∀ G x G' x', F.mem G x → F.mem G' x' → SubInst G' x' G x → p G' x' ≤ p G x

lemma supp_subset {x' x : V → Option α} (h : ∀ v, (x' v).isSome → (x v).isSome) :
    supp x' ⊆ supp x := fun v hv => h v hv

lemma res_le_res {G : SimpleGraph V} {x' x : V → Option α}
    (h : ∀ v, (x' v).isSome → (x v).isSome) : res G x' ≤ res G x :=
  fun _ _ hu => ⟨hu.1, h _ hu.2.1, h _ hu.2.2⟩

lemma neighborSet_res_subset (G : SimpleGraph V) (x : V → Option α) (v : V) :
    (res G x).neighborSet v ⊆ supp x := fun _ hw => hw.2.2

/-- On a finite instance, `maxDeg` bounds the degree of every node. -/
lemma ncard_neighborSet_le_maxDeg {G : SimpleGraph V} {x : V → Option α} (hx : (supp x).Finite)
    {v : V} (hv : (x v).isSome) : ((res G x).neighborSet v).ncard ≤ maxDeg G x :=
  le_csSup (hx.image _).bddAbove ⟨v, hv, rfl⟩

/-- On a nonempty finite instance, `maxDeg` is the degree of some node. -/
lemma exists_maxDeg_eq {G : SimpleGraph V} {x : V → Option α} (hx : (supp x).Finite)
    (hne : (supp x).Nonempty) : ∃ v, (x v).isSome ∧ ((res G x).neighborSet v).ncard = maxDeg G x := by
  obtain ⟨v, hv, h⟩ := Set.Nonempty.csSup_mem (α := ℕ) (hne.image _) (hx.image _)
  exact ⟨v, hv, h⟩

/-- `n` is non-decreasing. -/
theorem numNodes_nonDecreasing : NonDecreasing (allFinite (V := V) (α := α)) numNodes :=
  fun _ _ _ _ hx _ hsub => Set.ncard_le_ncard (supp_subset hsub.1) hx.2

/-- `Δ` is non-decreasing. -/
theorem maxDeg_nonDecreasing : NonDecreasing (allFinite (V := V) (α := α)) maxDeg := by
  intro G x G' x' hx _ hsub
  by_cases hne : (supp x').Nonempty
  · refine csSup_le (hne.image _) ?_
    rintro _ ⟨v, hv, rfl⟩
    refine le_trans ?_ (ncard_neighborSet_le_maxDeg hx.2 (hsub.1 v hv))
    exact Set.ncard_le_ncard (fun w hw => hsub.2.2 hw)
      (hx.2.subset (neighborSet_res_subset G x v))
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [maxDeg, hne]

/-- Observation 3.1(2): a pruning algorithm that leaves the inputs of the non-pruned nodes
unchanged is monotone with respect to every non-decreasing parameter. -/
theorem observation_3_1_2 {Pb : Problem V α β} {F : Family V α} (P : Pruning Pb F)
    (hP : ∀ G x ŷ v, P.prune G x ŷ v = none ∨ P.prune G x ŷ v = x v) {p : Param V α}
    (hp : NonDecreasing F p) : P.Monotone p := by
  intro G x ŷ hx
  refine hp _ _ _ _ hx (P.mem G x ŷ hx) ⟨P.sub G x ŷ, fun v hv => ?_, ?_⟩
  · rcases hP G x ŷ v with h | h
    · simp [h] at hv
    · exact h
  · rw [res_res (fun v h => h)]
    exact res_le_res (P.sub G x ŷ)

/-! ### Pruning rules: prune a locally defined set of nodes, keep the other inputs -/

/-- The pruning rule that prunes the nodes satisfying `W` in the current graph `res G x` and keeps
the inputs of the other nodes. -/
noncomputable def pruneBy (W : SimpleGraph V → (V → β) → V → Prop) (G : SimpleGraph V)
    (x : V → Option α) (ŷ : V → β) (v : V) : Option α :=
  open Classical in if W (res G x) ŷ v then none else x v

lemma pruneBy_isSome {W : SimpleGraph V → (V → β) → V → Prop} {G : SimpleGraph V}
    {x : V → Option α} {ŷ : V → β} {v : V} :
    (pruneBy W G x ŷ v).isSome ↔ (x v).isSome ∧ ¬ W (res G x) ŷ v := by
  unfold pruneBy; split_ifs with h <;> simp [h]

lemma pruneBy_cases (W : SimpleGraph V → (V → β) → V → Prop) (G : SimpleGraph V)
    (x : V → Option α) (ŷ : V → β) (v : V) :
    pruneBy W G x ŷ v = none ∨ pruneBy W G x ŷ v = x v := by
  unfold pruneBy; split_ifs <;> simp

lemma pruneBy_sub (W : SimpleGraph V → (V → β) → V → Prop) (G : SimpleGraph V)
    (x : V → Option α) (ŷ : V → β) (v : V) : (pruneBy W G x ŷ v).isSome → (x v).isSome :=
  fun h => (pruneBy_isSome.1 h).1

lemma allFinite_mem_pruneBy (W : SimpleGraph V → (V → β) → V → Prop) (G : SimpleGraph V)
    (x : V → Option α) (ŷ : V → β) (hx : (allFinite (V := V) (α := α)).mem G x) :
    allFinite.mem (res G (pruneBy W G x ŷ)) (pruneBy W G x ŷ) :=
  ⟨res_res (fun _ h => h), hx.2.subset (supp_subset (pruneBy_sub W G x ŷ))⟩

lemma viewEq_comp {R : ℕ} {γ δ : Type*} {G G' : SimpleGraph V} {z z' : V → γ} {v : V}
    (h : ViewEq R G z G' z' v) (f : γ → δ) : ViewEq R G (f ∘ z) G' (f ∘ z') v :=
  ⟨h.1, fun u hu => by simp [h.2 u hu]⟩

/-- A pruning rule given by an `R`-local predicate `W` is computed in `R` rounds. -/
lemma isLocal_pruneBy {R : ℕ} (W : SimpleGraph V → (V → β) → V → Prop)
    (hW : ∀ H ŷ H' ŷ' v, ViewEq R H ŷ H' ŷ' v → (W H ŷ v ↔ W H' ŷ' v)) :
    IsLocal R (fun G (z : V → Option α × β) =>
      pruneBy W G (fun v => (z v).1) (fun v => (z v).2)) := by
  intro G z G' z' v h
  have h1 := viewEq_res (x := fun v => (z v).1) (x' := fun v => (z' v).1) (viewEq_comp h Prod.fst)
  have h2 : ViewEq R (res G (fun v => (z v).1)) (fun v => (z v).2)
      (res G' (fun v => (z' v).1)) (fun v => (z' v).2) v :=
    ⟨h1.1, fun u hu => by
      simp [h.2 u ((edist_anti (res_le _ _)).trans hu)]⟩
  have h3 : (z v).1 = (z' v).1 := by rw [h.2 v (by simp)]
  have h4 := hW _ _ _ _ _ h2
  show pruneBy W G _ _ v = pruneBy W G' _ _ v
  unfold pruneBy
  beta_reduce
  rw [h3]
  by_cases hw : W (res G fun v => (z v).1) (fun v => (z v).2) v
  · rw [ite_eq_left hw, ite_eq_left (h4.1 hw)]
  · rw [ite_eq_right hw, ite_eq_right (fun h => hw (h4.2 h))]

lemma edist_le_succ_of_adj {H : SimpleGraph V} {u v w : V} {m : ℕ} (h : H.edist u v ≤ m)
    (hvw : H.Adj v w) : H.edist u w ≤ (m + 1 : ℕ) :=
  edist_le_natCast_add h (by simp [edist_eq_one_iff_adj.2 hvw])

/-- A node at finite positive distance from another node in `res G x` is a node of the instance. -/
lemma isSome_of_edist_res {G : SimpleGraph V} {x : V → Option α} {u v : V} {m : ℕ}
    (h : (res G x).edist u v ≤ m) (huv : u ≠ v) : (x v).isSome := by
  obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.1 (edist_ne_top_of_le_natCast h)
  cases j with
  | zero =>
    have h0 : (res G x).edist u v = 0 := by rw [← hj]; simp
    exact absurd (edist_eq_zero_iff.1 h0) huv
  | succ j =>
    obtain ⟨y, -, hy⟩ := exists_adj_of_edist_eq_succ hj.symm
    exact hy.2.2

/-! ### `(2, β)`-ruling sets and MIS (Observation 3.2) -/

/-- The `(2, β)`-ruling set problem: the output `true` marks the set `S`; `S` is independent and
every node of the instance not in `S` is at distance at most `β` from a node of `S`. -/
def rulingSet (β : ℕ) : Problem V α Bool where
  sol G x y := (∀ u v, (res G x).Adj u v → ¬ (y u = true ∧ y v = true)) ∧
    ∀ u, (x u).isSome → y u = false → ∃ v, (x v).isSome ∧ y v = true ∧ (res G x).edist u v ≤ β
  congr {G x y y'} h hs := by
    refine ⟨fun u v huv => ?_, fun u hu hyu => ?_⟩
    · rw [← h u huv.2.1, ← h v huv.2.2]; exact hs.1 u v huv
    · obtain ⟨v, hv, hyv, hd⟩ := hs.2 u hu (by rw [h u hu]; exact hyu)
      exact ⟨v, hv, by rw [← h v hv]; exact hyv, hd⟩
  empty := ⟨fun _ => false, by simp⟩

/-- MIS is the `(2, 1)`-ruling set problem. -/
abbrev mis : Problem V α Bool := rulingSet 1

/-- `v` is selected and has no selected neighbour in `H`. -/
def IsoTrue (H : SimpleGraph V) (ŷ : V → Bool) (v : V) : Prop :=
  ŷ v = true ∧ ∀ w, H.Adj v w → ŷ w = false

/-- The set `W` of nodes pruned by `P_(2,β)` (page 10): selected nodes without selected
neighbours, and non-selected nodes at distance at most `β` from such a node. -/
def rulingW (β : ℕ) (H : SimpleGraph V) (ŷ : V → Bool) (u : V) : Prop :=
  IsoTrue H ŷ u ∨ (ŷ u = false ∧ ∃ v, H.edist u v ≤ β ∧ IsoTrue H ŷ v)

lemma isoTrue_iff_of_viewEq {R m : ℕ} {H H' : SimpleGraph V} {ŷ ŷ' : V → Bool} {u v : V}
    (h : ViewEq R H ŷ H' ŷ' u) (hv : H.edist u v ≤ m) (hm : m + 1 ≤ R) :
    IsoTrue H ŷ v ↔ IsoTrue H' ŷ' v := by
  have hvR : H.edist u v < R := lt_of_le_of_lt hv (by exact_mod_cast (by omega : m < R))
  unfold IsoTrue
  rw [h.2 v hvR.le]
  refine and_congr_right' (forall_congr' fun w => ?_)
  rw [h.1 hvR w]
  refine imp_congr_right fun hw => ?_
  rw [h.2 w ((edist_le_succ_of_adj hv ((h.1 hvR w).2 hw)).trans (by exact_mod_cast hm))]

lemma rulingW_iff_of_viewEq {β : ℕ} {H H' : SimpleGraph V} {ŷ ŷ' : V → Bool} {u : V}
    (h : ViewEq (β + 1) H ŷ H' ŷ' u) : rulingW β H ŷ u ↔ rulingW β H' ŷ' u := by
  unfold rulingW
  rw [isoTrue_iff_of_viewEq (m := 0) h (by simp) (by omega), h.2 u (by simp)]
  refine or_congr_right (and_congr_right' (exists_congr fun v => ?_))
  rw [h.1.edist_le_iff (by omega)]
  exact and_congr_right fun hv => isoTrue_iff_of_viewEq h hv le_rfl

/-- The pruning algorithm `P_(2,β)` for the `(2, β)`-ruling set problem (page 10), for `β ≥ 1`. -/
noncomputable def rulingPruning (β : ℕ) (hβ : 1 ≤ β) :
    Pruning (rulingSet β) (allFinite (V := V) (α := α)) where
  prune := pruneBy (rulingW β)
  rad := β + 1
  isLocal := isLocal_pruneBy _ fun _ _ _ _ _ h => rulingW_iff_of_viewEq h
  sub := pruneBy_sub _
  mem G x ŷ hx := allFinite_mem_pruneBy _ G x ŷ hx
  detect G x ŷ _ hs v := by
    unfold pruneBy
    by_cases hv : (x v).isSome
    · have iso : ∀ w, (x w).isSome → ŷ w = true → IsoTrue (res G x) ŷ w :=
        fun w _ hw => ⟨hw, fun w' hww' => by
          cases h' : ŷ w'
          · rfl
          · exact absurd ⟨hw, h'⟩ (hs.1 w w' hww')⟩
      rw [ite_eq_left]
      cases hy : ŷ v
      · obtain ⟨w, hw, hyw, hd⟩ := hs.2 v hv hy
        exact Or.inr ⟨hy, w, hd, iso w hw hyw⟩
      · exact Or.inl (iso v hv hy)
    · split_ifs <;> simp_all
  glue G x ŷ y' hx hs := by
    set x' := pruneBy (rulingW β) G x ŷ with hx'
    set y := fun v => if (x' v).isSome then y' v else ŷ v
    have hyp : ∀ v, (x' v).isSome = false → y v = ŷ v := fun v h => by simp [y, h]
    have hyk : ∀ v, (x' v).isSome = true → y v = y' v := fun v h => by simp [y, h]
    -- a node of the instance is pruned iff it is in `W`
    have hW : ∀ v, (x v).isSome → ((x' v).isSome = false ↔ rulingW β (res G x) ŷ v) := by
      intro v hv
      rw [hx', Bool.eq_false_iff, ne_eq, pruneBy_isSome]
      simp [hv]
    have hres : res G x' ≤ res G x := res_le_res (pruneBy_sub _ G x ŷ)
    obtain ⟨hs1, hs2⟩ := hs
    rw [res_res (fun _ h => h)] at hs1 hs2
    refine ⟨fun u v huv ⟨hu, hv⟩ => ?_, fun u hu hyu => ?_⟩
    · cases hu' : (x' u).isSome <;> cases hv' : (x' v).isSome
      · -- both pruned: `u` is selected, so it has no selected neighbour
        rw [hyp u hu', hyp v hv'] at *
        rcases (hW u huv.2.1).1 hu' with h | h
        · exact absurd (h.2 v huv) (by simp [hv])
        · simp [hu] at h
      · -- `u` pruned, `v` kept: `v` would be pruned, being next to an isolated selected node
        rw [hyp u hu'] at hu
        rcases (hW u huv.2.1).1 hu' with h | h
        · have hvW : rulingW β (res G x) ŷ v := by
            refine Or.inr ⟨h.2 v huv, u, ?_, h⟩
            rw [SimpleGraph.edist_comm, edist_eq_one_iff_adj.2 huv]; exact_mod_cast hβ
          simp [(hW v huv.2.2).2 hvW] at hv'
        · simp [hu] at h
      · rw [hyp v hv'] at hv
        rcases (hW v huv.2.2).1 hv' with h | h
        · have huW : rulingW β (res G x) ŷ u := by
            refine Or.inr ⟨h.2 u huv.symm, v, ?_, h⟩
            rw [edist_eq_one_iff_adj.2 huv]; exact_mod_cast hβ
          simp [(hW u huv.2.1).2 huW] at hu'
        · simp [hv] at h
      · rw [hyk u hu', hyk v hv'] at *
        exact hs1 u v ⟨huv.1, hu', hv'⟩ ⟨hu, hv⟩
    · cases hu' : (x' u).isSome
      · rw [hyp u hu'] at hyu
        rcases (hW u hu).1 hu' with h | ⟨-, v, hd, hv⟩
        · simp [IsoTrue, hyu] at h
        · have huv : u ≠ v := by rintro rfl; simp [IsoTrue, hyu] at hv
          have hvx := isSome_of_edist_res hd huv
          refine ⟨v, hvx, ?_, hd⟩
          rw [hyp v ((hW v hvx).2 (Or.inl hv))]; exact hv.1
      · rw [hyk u hu'] at hyu
        obtain ⟨v, hv, hyv, hd⟩ := hs2 u hu' hyu
        exact ⟨v, pruneBy_sub _ G x ŷ v hv, by rw [hyk v hv]; exact hyv,
          (edist_anti hres).trans hd⟩

/-- Observation 3.2: `P_(2,β)` is a pruning algorithm for the `(2, β)`-ruling set problem running
in `β + 1` rounds (for `β ≥ 1`), and it is monotone with respect to `n` and `Δ` (indeed with
respect to every non-decreasing parameter). -/
theorem observation_3_2 (β : ℕ) (hβ : 1 ≤ β) :
    (rulingPruning (V := V) (α := α) β hβ).rad = β + 1 ∧
    (rulingPruning (V := V) (α := α) β hβ).Monotone numNodes ∧
    (rulingPruning (V := V) (α := α) β hβ).Monotone maxDeg ∧
    ∀ p, NonDecreasing allFinite p → (rulingPruning (V := V) (α := α) β hβ).Monotone p :=
  ⟨rfl, observation_3_1_2 _ (pruneBy_cases _) numNodes_nonDecreasing,
    observation_3_1_2 _ (pruneBy_cases _) maxDeg_nonDecreasing,
    fun _ hp => observation_3_1_2 _ (pruneBy_cases _) hp⟩

/-- In particular, `P_(2,1)` is a pruning algorithm for MIS running in 2 rounds. -/
noncomputable def misPruning : Pruning (mis (V := V) (α := α)) allFinite :=
  rulingPruning 1 le_rfl


/-! ### Maximal matching with the paper's encoding: Observation 3.3 fails -/

lemma pruneBy_eq_none {W : SimpleGraph V → (V → β) → V → Prop} {G : SimpleGraph V}
    {x : V → Option α} {ŷ : V → β} {v : V} (h : (x v).isSome → W (res G x) ŷ v) :
    pruneBy W G x ŷ v = none := by
  unfold pruneBy
  split_ifs with hW
  · rfl
  · cases hx : x v with
    | none => rfl
    | some a => exact absurd (h (by simp [hx])) hW

lemma pruneBy_isSome_eq_false {W : SimpleGraph V → (V → β) → V → Prop} {G : SimpleGraph V}
    {x : V → Option α} {ŷ : V → β} {v : V} (hv : (x v).isSome) :
    (pruneBy W G x ŷ v).isSome = false ↔ W (res G x) ŷ v := by
  rw [Bool.eq_false_iff, ne_eq, pruneBy_isSome]
  simp [hv]

/-- The paper's notion of matched nodes (page 6): `u` and `v` are neighbours with the same output,
and no other neighbour of `u` or of `v` has this output. -/
def MatchedPaper (H : SimpleGraph V) (y : V → ℕ) (u v : V) : Prop :=
  H.Adj u v ∧ y u = y v ∧ ∀ w, (H.Adj u w ∨ H.Adj v w) → w ≠ u → w ≠ v → y w ≠ y u

lemma matchedPaper_congr_aux {G : SimpleGraph V} {x : V → Option α} {y y' : V → ℕ}
    (h : ∀ v, (x v).isSome → y v = y' v) {u v : V} :
    MatchedPaper (res G x) y u v → MatchedPaper (res G x) y' u v := by
  rintro ⟨huv, he, hw⟩
  refine ⟨huv, by rw [← h u huv.2.1, ← h v huv.2.2]; exact he, fun w hw' h1 h2 => ?_⟩
  have hwx : (x w).isSome := hw'.elim (·.2.2) (·.2.2)
  rw [← h w hwx, ← h u huv.2.1]
  exact hw w hw' h1 h2

lemma matchedPaper_congr {G : SimpleGraph V} {x : V → Option α} {y y' : V → ℕ}
    (h : ∀ v, (x v).isSome → y v = y' v) (u v : V) :
    MatchedPaper (res G x) y u v ↔ MatchedPaper (res G x) y' u v :=
  ⟨matchedPaper_congr_aux h, matchedPaper_congr_aux fun v hv => (h v hv).symm⟩

/-- Maximal matching with the paper's encoding (page 6): every node of the instance is matched to
a neighbour, or each of its neighbours is matched to one of its own neighbours. -/
def mmPaper : Problem V α ℕ where
  sol G x y := ∀ u, (x u).isSome → (∃ v, MatchedPaper (res G x) y u v) ∨
    ∀ v, (res G x).Adj u v → ∃ w, MatchedPaper (res G x) y v w
  congr {G x y y'} h hs u hu := by simpa only [matchedPaper_congr h] using hs u hu
  empty := ⟨fun _ => 0, fun u hu => by simp at hu⟩

lemma mmPaper_sol_iff {G : SimpleGraph V} {x : V → Option α} {y : V → ℕ} :
    (mmPaper (V := V) (α := α)).sol G x y ↔ ∀ u, (x u).isSome →
      (∃ v, MatchedPaper (res G x) y u v) ∨
        ∀ v, (res G x).Adj u v → ∃ w, MatchedPaper (res G x) y v w := Iff.rfl

/-- The set `W` of nodes pruned by the paper's `P_MM` (page 10): nodes matched to a neighbour, and
nodes all of whose neighbours are matched to some other node. -/
def mmPaperW (H : SimpleGraph V) (y : V → ℕ) (u : V) : Prop :=
  (∃ v, MatchedPaper H y u v) ∨ ∀ v, H.Adj u v → ∃ w, w ≠ u ∧ MatchedPaper H y v w

instance res.decidableAdj {G : SimpleGraph V} [DecidableRel G.Adj] {x : V → Option α} :
    DecidableRel (res G x).Adj :=
  fun u w => decidable_of_iff (G.Adj u w ∧ (x u).isSome ∧ (x w).isSome) res_adj.symm

instance MatchedPaper.decidable [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    [DecidableRel H.Adj] {y : V → ℕ} {u v : V} : Decidable (MatchedPaper H y u v) := by
  unfold MatchedPaper; infer_instance

instance mmPaperW.decidable [Fintype V] [DecidableEq V] {H : SimpleGraph V}
    [DecidableRel H.Adj] {y : V → ℕ} {u : V} : Decidable (mmPaperW H y u) := by
  unfold mmPaperW; infer_instance

/-- The path `0 — 1 — 2 — 3` (in the paper's notation for the counterexample: `v₀ — u₀ — u — v`). -/
def path4 : SimpleGraph (Fin 4) where
  Adj a b := a.val + 1 = b.val ∨ b.val + 1 = a.val
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by omega⟩

instance : DecidableRel path4.Adj := fun a b =>
  decidable_of_iff (a.val + 1 = b.val ∨ b.val + 1 = a.val) Iff.rfl

/-- The tentative output of the counterexample: `v₀, u₀` are matched (output `5`), `u` and `v`
are unmatched. -/
def mmCexOut : Fin 4 → ℕ := ![5, 5, 1, 2]

/-- On the counterexample, the paper's `P_MM` prunes exactly `v₀` and `u₀`. -/
lemma mmPaperW_cex :
    ∀ v, mmPaperW (res path4 fun _ => some ()) mmCexOut v ↔ v = 0 ∨ v = 1 := by
  decide

/-- Gluing fails on the counterexample: the residual instance (the edge `u — v`) is solved by the
output `5` at both nodes, but the combined output (`5` everywhere) is not a maximal matching of the
path. -/
lemma mmPaper_cex :
    (mmPaper (α := Unit)).sol path4 ![none, none, some (), some ()] (fun _ => 5) ∧
    ¬ (mmPaper (α := Unit)).sol path4 (fun _ => some ()) (fun _ => 5) := by
  rw [mmPaper_sol_iff, mmPaper_sol_iff]
  refine ⟨by decide, ?_⟩
  have : res path4 (fun _ : Fin 4 => some ()) = path4 := by ext; simp
  rw [this]
  decide

/-- **Observation 3.3 is false.** There is no pruning algorithm for maximal matching (with the
paper's encoding, on the family of all finite instances) whose set of pruned nodes is the set `W`
of the paper's algorithm `P_MM` — whatever new inputs it gives to the remaining nodes. Gluing fails
on the path `v₀ — u₀ — u — v` with tentative output `(5, 5, 1, 2)`: `W = {v₀, u₀}`, the residual
edge `u — v` is solved by `(5, 5)`, and the combined output `(5, 5, 5, 5)` matches nobody. -/
theorem observation_3_3_false :
    ¬ ∃ P : Pruning (mmPaper (V := Fin 4) (α := Unit)) allFinite,
      ∀ G x ŷ v, P.prune G x ŷ v = none ↔ (x v = none ∨ mmPaperW (res G x) ŷ v) := by
  rintro ⟨P, hP⟩
  set x : Fin 4 → Option Unit := fun _ => some ()
  set x₀ : Fin 4 → Option Unit := ![none, none, some (), some ()]
  have hmem : (allFinite (V := Fin 4) (α := Unit)).mem path4 x :=
    ⟨by ext; simp [x], Set.toFinite _⟩
  set x' := P.prune path4 x mmCexOut
  have key : ∀ v, x' v = none ↔ x₀ v = none := by
    intro v
    rw [hP]
    revert v
    decide
  have hsupp : ∀ v, (x' v).isSome ↔ (x₀ v).isSome := fun v => by
    simp only [Option.isSome_iff_ne_none, ne_eq, key v]
  have hsol : (mmPaper (V := Fin 4) (α := Unit)).sol (res path4 x') x' (fun _ => 5) := by
    rw [mmPaper_sol_iff, res_res (fun _ h => h), res_congr hsupp]
    simp_rw [hsupp]
    exact (mmPaper_sol_iff (G := path4) (x := x₀)).1 mmPaper_cex.1
  have hglue := P.glue path4 x mmCexOut (fun _ => 5) hmem hsol
  have hŷ : ∀ v, x₀ v = none → mmCexOut v = 5 := by decide
  have hc : (fun v => if (x' v).isSome then 5 else mmCexOut v) = fun _ => 5 := by
    funext v
    split_ifs with h
    · rfl
    · exact hŷ v ((key v).1 (by simpa using h))
  rw [hc] at hglue
  exact mmPaper_cex.2 hglue

/-! ### Maximal matching with partner identities: the repaired Observation 3.3 -/

/-- `u` and `v` are matched: neighbours pointing to each other (outputs are partner identities). -/
def MatchedId (H : SimpleGraph V) (y : V → Option V) (u v : V) : Prop :=
  H.Adj u v ∧ y u = some v ∧ y v = some u

lemma MatchedId.symm {H : SimpleGraph V} {y : V → Option V} {u v : V} (h : MatchedId H y u v) :
    MatchedId H y v u := ⟨h.1.symm, h.2.2, h.2.1⟩

lemma matchedId_congr {G : SimpleGraph V} {x : V → Option α} {y y' : V → Option V}
    (h : ∀ v, (x v).isSome → y v = y' v) (u v : V) :
    MatchedId (res G x) y u v ↔ MatchedId (res G x) y' u v := by
  unfold MatchedId
  refine and_congr_right fun huv => ?_
  rw [h u huv.2.1, h v huv.2.2]

/-- Maximal matching, the matching being encoded by partner identities: every node of the instance
is matched to a neighbour, or each of its neighbours is matched to one of its own neighbours. -/
def mmId : Problem V α (Option V) where
  sol G x y := ∀ u, (x u).isSome → (∃ v, MatchedId (res G x) y u v) ∨
    ∀ v, (res G x).Adj u v → ∃ w, MatchedId (res G x) y v w
  congr {G x y y'} h hs u hu := by simpa only [matchedId_congr h] using hs u hu
  empty := ⟨fun _ => none, fun u hu => by simp at hu⟩

/-- The set of nodes pruned by the repaired `P_MM`: nodes matched to a neighbour, and nodes all of
whose neighbours are matched to some other node. -/
def mmIdW (H : SimpleGraph V) (y : V → Option V) (u : V) : Prop :=
  (∃ v, MatchedId H y u v) ∨ ∀ v, H.Adj u v → ∃ w, w ≠ u ∧ MatchedId H y v w

lemma matchedId_iff_of_viewEq {R m : ℕ} {H H' : SimpleGraph V} {y y' : V → Option V} {u v w : V}
    (h : ViewEq R H y H' y' u) (hv : H.edist u v ≤ m) (hm : m + 1 ≤ R) :
    MatchedId H y v w ↔ MatchedId H' y' v w := by
  have hvR : H.edist u v < R := lt_of_le_of_lt hv (by exact_mod_cast (by omega : m < R))
  have hw : H'.Adj v w → y w = y' w := fun ha =>
    h.2 w ((edist_le_succ_of_adj hv ((h.1 hvR w).2 ha)).trans (by exact_mod_cast hm))
  unfold MatchedId
  rw [h.1 hvR w, h.2 v hvR.le]
  refine and_congr_right fun ha => and_congr_right' ?_
  rw [hw ha]

lemma mmIdW_iff_of_viewEq {H H' : SimpleGraph V} {y y' : V → Option V} {u : V}
    (h : ViewEq 2 H y H' y' u) : mmIdW H y u ↔ mmIdW H' y' u := by
  unfold mmIdW
  refine or_congr (exists_congr fun v => matchedId_iff_of_viewEq (m := 0) h (by simp) (by omega))
    (forall_congr' fun v => ?_)
  rw [← h.1 (by simp) v]
  refine imp_congr_right fun ha => exists_congr fun w =>
    and_congr_right' (matchedId_iff_of_viewEq (m := 1) h ?_ le_rfl)
  simp [edist_eq_one_iff_adj.2 ha]

/-- The repaired pruning algorithm `P_MM` for maximal matching encoded by partner identities. It
runs in 2 rounds (the paper's `P_MM` needs 3 because of its encoding). -/
noncomputable def mmPruning : Pruning (mmId (V := V) (α := α)) allFinite where
  prune := pruneBy mmIdW
  rad := 2
  isLocal := isLocal_pruneBy _ fun _ _ _ _ _ h => mmIdW_iff_of_viewEq h
  sub := pruneBy_sub _
  mem G x ŷ hx := allFinite_mem_pruneBy _ G x ŷ hx
  detect G x ŷ _ hs v := pruneBy_eq_none fun hv => by
    rcases hs v hv with hm | hall
    · exact Or.inl hm
    · by_cases hm : ∃ w, MatchedId (res G x) ŷ v w
      · exact Or.inl hm
      · refine Or.inr fun w hw => ?_
        obtain ⟨w', hm'⟩ := hall w hw
        refine ⟨w', ?_, hm'⟩
        rintro rfl
        exact hm ⟨w, hm'.symm⟩
  glue G x ŷ y' hx hs := by
    set x' := pruneBy mmIdW G x ŷ with hx'
    set y := fun v => if (x' v).isSome then y' v else ŷ v
    have hyp : ∀ v, (x' v).isSome = false → y v = ŷ v := fun v h => by simp [y, h]
    have hyk : ∀ v, (x' v).isSome = true → y v = y' v := fun v h => by simp [y, h]
    have hW : ∀ v, (x v).isSome → ((x' v).isSome = false ↔ mmIdW (res G x) ŷ v) :=
      fun v hv => pruneBy_isSome_eq_false hv
    have hres : res G x' ≤ res G x := res_le_res (pruneBy_sub _ G x ŷ)
    have hs' : ∀ u, (x' u).isSome → (∃ v, MatchedId (res G x') y' u v) ∨
        ∀ v, (res G x').Adj u v → ∃ w, MatchedId (res G x') y' v w := by
      have := hs
      simp only [mmId, res_res (fun _ h => h)] at this
      exact this
    -- matched pairs of `ŷ` are pruned, so they stay matched
    have hpm : ∀ u v, MatchedId (res G x) ŷ u v → MatchedId (res G x) y u v := by
      intro u v hm
      have hu := (hW u hm.1.2.1).2 (Or.inl ⟨v, hm⟩)
      have hv := (hW v hm.1.2.2).2 (Or.inl ⟨u, hm.symm⟩)
      exact ⟨hm.1, by rw [hyp u hu]; exact hm.2.1, by rw [hyp v hv]; exact hm.2.2⟩
    -- matched pairs of `y'` stay matched
    have hkm : ∀ u v, MatchedId (res G x') y' u v → MatchedId (res G x) y u v := by
      intro u v hm
      exact ⟨hres hm.1, by rw [hyk u hm.1.2.1]; exact hm.2.1, by rw [hyk v hm.1.2.2]; exact hm.2.2⟩
    intro u hu
    cases hu' : (x' u).isSome
    · rcases (hW u hu).1 hu' with ⟨v, hm⟩ | hall
      · exact Or.inl ⟨v, hpm u v hm⟩
      · refine Or.inr fun v hv => ?_
        obtain ⟨w, -, hm⟩ := hall v hv
        exact ⟨w, hpm v w hm⟩
    · rcases hs' u hu' with ⟨v, hm⟩ | hall
      · exact Or.inl ⟨v, hkm u v hm⟩
      · refine Or.inr fun v hv => ?_
        cases hv' : (x' v).isSome
        · rcases (hW v hv.2.2).1 hv' with ⟨w, hm⟩ | hall'
          · exact ⟨w, hpm v w hm⟩
          · obtain ⟨w, -, hm⟩ := hall' u hv.symm
            have := (hW u hu).2 (Or.inl ⟨w, hm⟩)
            simp [hu'] at this
        · obtain ⟨w, hm⟩ := hall v ⟨hv.1, hu', hv'⟩
          exact ⟨w, hkm v w hm⟩

/-- Observation 3.3, repaired: with the matching encoded by partner identities, the analogue of
`P_MM` is a pruning algorithm for maximal matching running in 2 rounds, monotone with respect to
`n` and `Δ` (indeed with respect to every non-decreasing parameter). -/
theorem observation_3_3_repaired :
    (mmPruning (V := V) (α := α)).rad = 2 ∧
    (mmPruning (V := V) (α := α)).Monotone numNodes ∧
    (mmPruning (V := V) (α := α)).Monotone maxDeg ∧
    ∀ p, NonDecreasing allFinite p → (mmPruning (V := V) (α := α)).Monotone p :=
  ⟨rfl, observation_3_1_2 _ (pruneBy_cases _) numNodes_nonDecreasing,
    observation_3_1_2 _ (pruneBy_cases _) maxDeg_nonDecreasing,
    fun _ hp => observation_3_1_2 _ (pruneBy_cases _) hp⟩

end Podc.UniformLocalAlgorithms
