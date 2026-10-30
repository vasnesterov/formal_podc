import Papers.PODC2016.SpaceTimeVerification.Crossing
import Papers.PODC2016.SpaceTimeVerification.LowerBound

/-!
# Proposition 4 and Theorem 5 hold in the anonymous model

`Crossing.lean` shows that Proposition 4 and Theorem 5 (the crossing tool) are false for `t ≥ 2`
when a node sees its labelled radius-`t` ball. Here we show that they are true in the *anonymous*
(identifier-free, broadcast) message-passing model, where what a node learns in `t` rounds is its
depth-`t` *view* (the depth-`t` truncation of its universal cover, with the states and labels
attached).

* `View α k`, `view G x k v`: the depth-`k` view of `v` in `G` with node data `x : V → α`:
  `view G x 0 v = x v`, `view G x (k+1) v = (x v, multiset of the depth-k views of the
  neighbours)`. An anonymous `t`-round verifier is a function of `view G (fun u => (I u, ℓ u)) t v`.
* `view_transport`: an isomorphism `σ` of the induced `t`-neighbourhoods `N_t(e) → N_t(e')`
  preserving data and endpoints preserves the depth-`m` view of every node `y` with
  `dist(y, endpoint) + m ≤ t`.
* `proposition_4_view`: under the hypotheses of Proposition 4 (and data-preserving `σ`), every
  node of the crossing `C(e, e', G)` has the same depth-`k` views (`k ≤ t`) as in `G`;
  `proposition_4_accept` derives that every node of every union of connected components of the
  crossing accepts if every node of `G` accepts.
* `proposition_4_anon`: the pigeonhole form of Proposition 4 (labels from `L`, `|L|^q < r`).
* `theorem_5_anon`: Theorem 5 in the anonymous model: every anonymous `t`-PLS uses at least
  `r^{1/q}` distinct labels on `G_s`, i.e. `r ≤ |L|^q`; `theorem_5_anon_length`: labels of
  length `≤ m` force `r ≤ 2^{(m+1)q}`, i.e. label size `Ω(log r / q)`.
* `triangles_view_eq`: on the counterexample of `Crossing.lean` (disjoint triangles, `t = 2`) the
  crossing does not change any depth-`2` view.

The paper's proof claims that every node of `N_t(e_i) ∪ N_t(e_j)` keeps "the same
`t`-neighbourhood"; this is false for balls but true for views: the view does not record which
neighbour is which, so replacing the neighbour `H` of `T` by `H'`, whose view is the same, leaves
the view of `T` unchanged.
-/

namespace Podc.SpaceTimeVerification

open SimpleGraph

/-! ### Views -/

/-- The type of depth-`k` views with node data in `α`: a depth-`0` view is the node's data, a
depth-`(k+1)` view is the node's data with the multiset of the depth-`k` views of its
neighbours. -/
def View (α : Type*) : ℕ → Type _
  | 0 => α
  | k + 1 => α × Multiset (View α k)

section Views

variable {V W α : Type*}

/-- The neighbours of `v` as a finset (the graph is on a finite vertex type). -/
noncomputable def nbrs [Finite V] (G : SimpleGraph V) (v : V) : Finset V :=
  (Set.toFinite (G.neighborSet v)).toFinset

@[simp] lemma mem_nbrs [Finite V] {G : SimpleGraph V} {v b : V} : b ∈ nbrs G v ↔ G.Adj v b := by
  simp [nbrs]

/-- The depth-`k` view of `v` in `G` with node data `x` (states and labels). This is exactly the
information `v` gathers in `k` rounds of *anonymous broadcast* message passing, where every node
initially knows its own data and in every round sends its whole current knowledge to all
neighbours (without identifiers or port numbers, a node receives the multiset of its neighbours'
messages). An anonymous `t`-round verifier is any function of `view G (fun u => (I u, ℓ u)) t v`. -/
noncomputable def view [Finite V] (G : SimpleGraph V) (x : V → α) : (k : ℕ) → V → View α k
  | 0, v => x v
  | k + 1, v => (x v, (nbrs G v).val.map (view G x k))

lemma view_zero [Finite V] (G : SimpleGraph V) (x : V → α) (v : V) : view G x 0 v = x v := rfl

lemma view_succ [Finite V] (G : SimpleGraph V) (x : V → α) (k : ℕ) (v : V) :
    view G x (k + 1) v = ((x v, (nbrs G v).val.map (view G x k)) : α × Multiset (View α k)) :=
  rfl

/-- Two depth-`(k+1)` views agree if the data agree and a bijection between the neighbourhoods
preserves the depth-`k` views. -/
lemma view_succ_eq [Finite V] [Finite W] {G : SimpleGraph V} {G' : SimpleGraph W} {x : V → α}
    {x' : W → α} {k : ℕ} {v : V} {w : W} {f : V → W} (hx : x' w = x v)
    (hf : Set.BijOn f (G.neighborSet v) (G'.neighborSet w))
    (hview : ∀ b, G.Adj v b → view G' x' k (f b) = view G x k b) :
    view G' x' (k + 1) w = view G x (k + 1) v := by
  rw [view_succ, view_succ, hx]
  congr 1
  symm
  refine Multiset.map_eq_map_of_bij_of_nodup _ _ (nbrs G v).nodup (nbrs G' w).nodup
    (fun b _ => f b) (fun b hb => ?_) (fun a ha b hb h => ?_) (fun b hb => ?_)
    (fun b hb => (hview b (mem_nbrs.1 hb)).symm)
  · exact mem_nbrs.2 (hf.mapsTo (mem_nbrs.1 hb))
  · exact hf.injOn (mem_nbrs.1 ha) (mem_nbrs.1 hb) h
  · obtain ⟨a, ha, rfl⟩ := hf.surjOn (mem_nbrs.1 hb)
    exact ⟨a, mem_nbrs.2 ha, rfl⟩

/-- Restricting to a union `K` of connected components does not change the views of its nodes. -/
lemma view_induce [Finite V] {G : SimpleGraph V} {K : Set V}
    (hK : ∀ a ∈ K, ∀ b, G.Adj a b → b ∈ K) (x : V → α) (k : ℕ) (w : K) :
    view (G.induce K) (x ∘ Subtype.val) k w = view G x k w.1 := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    symm
    refine view_succ_eq rfl ⟨fun b hb => ?_, Subtype.val_injective.injOn, fun b hb => ?_⟩
      (fun b _ => (ih b).symm)
    · simpa using hb
    · exact ⟨⟨b, hK _ w.2 _ hb⟩, by simpa using hb, rfl⟩

end Views

/-! ### Transport along an isomorphism of edge neighbourhoods -/

section Transport

variable {V α : Type*} {G : SimpleGraph V} {t : ℕ} {N : Set V} {σ : V → V}

/-- A map `σ` preserving adjacency on `N` does not increase the distance to a
node `u` whose `t`-ball lies in `N`, for nodes at distance `≤ t` from `u`. -/
lemma edist_map_le (hadj : ∀ a ∈ N, ∀ b ∈ N, G.Adj a b → G.Adj (σ a) (σ b))
    {u : V} (hu : ∀ w, G.edist w u ≤ t → w ∈ N) {y : V} (hy : G.edist y u ≤ t) :
    G.edist (σ y) (σ u) ≤ G.edist y u := by
  have aux : ∀ (y : V) (p : G.Walk y u), (p.length : ℕ∞) ≤ t →
      ∃ q : G.Walk (σ y) (σ u), q.length = p.length := by
    intro y p
    clear hy
    induction p with
    | nil => exact fun _ => ⟨Walk.nil, rfl⟩
    | @cons a b _ h p ih =>
      intro hp
      have hp' : (p.length : ℕ∞) ≤ t := le_trans (by simp) hp
      obtain ⟨q, hq⟩ := ih hu hp'
      have ha : a ∈ N := hu a (le_trans (edist_le _) hp)
      have hb : b ∈ N := hu b (le_trans (edist_le _) hp')
      exact ⟨Walk.cons (hadj a ha b hb h) q, by simp [hq]⟩
  obtain ⟨p, hp⟩ := exists_walk_of_edist_ne_top (ne_top_of_le_ne_top (by simp) hy)
  obtain ⟨q, hq⟩ := aux y p (hp ▸ hy)
  rw [← hp, ← hq]
  exact edist_le q

lemma edist_succ_le_of_adj {u y b : V} (h : G.Adj y b) : G.edist b u ≤ G.edist y u + 1 := by
  calc G.edist b u ≤ G.edist b y + G.edist y u := SimpleGraph.edist_triangle
    _ = G.edist y u + 1 := by rw [edist_eq_one_iff_adj.2 h.symm, add_comm]

lemma mem_edgeNbhd_left {e : V × V} {w : V} (h : G.edist w e.1 ≤ t) : w ∈ edgeNbhd G t e :=
  Or.inl h

lemma mem_edgeNbhd_right {e : V × V} {w : V} (h : G.edist w e.2 ≤ t) : w ∈ edgeNbhd G t e :=
  Or.inr h

/-- **Transport lemma.** Let `σ` be an isomorphism of the induced `t`-neighbourhoods
`N_t(e) → N_t(e')` (a bijection preserving adjacency in both directions) which maps tail to tail,
head to head and preserves the node data `x`. Then `σ` preserves the depth-`m` view of every node
`y` with `dist(y, T(e)) + m ≤ t` or `dist(y, H(e)) + m ≤ t`. -/
theorem view_transport [Finite V] {x : V → α} {e e' : V × V}
    (hσ : Set.BijOn σ (edgeNbhd G t e) (edgeNbhd G t e'))
    (hadj : ∀ a ∈ edgeNbhd G t e, ∀ b ∈ edgeNbhd G t e, (G.Adj a b ↔ G.Adj (σ a) (σ b)))
    (h1 : σ e.1 = e'.1) (h2 : σ e.2 = e'.2) (hx : ∀ a ∈ edgeNbhd G t e, x (σ a) = x a) :
    ∀ (m : ℕ) (y : V), (G.edist y e.1 + m ≤ t ∨ G.edist y e.2 + m ≤ t) →
      view G x m (σ y) = view G x m y := by
  have hdist : ∀ y, ∀ u u', σ u = u' → (∀ w, G.edist w u ≤ t → w ∈ edgeNbhd G t e) →
      G.edist y u ≤ t → G.edist (σ y) u' ≤ G.edist y u := by
    intro y u u' hu' hu hy
    rw [← hu']
    exact edist_map_le (fun a ha b hb => (hadj a ha b hb).1) hu hy
  intro m
  induction m with
  | zero =>
    intro y hy
    have hyN : y ∈ edgeNbhd G t e := by
      rcases hy with hy | hy
      · exact mem_edgeNbhd_left (by simpa using hy)
      · exact mem_edgeNbhd_right (by simpa using hy)
    exact hx y hyN
  | succ m ih =>
    intro y hy
    -- `y` and all its neighbours lie in `N_t(e)`, `σ y` and all its neighbours in `N_t(e')`
    have key : ∀ u u', σ u = u' → (∀ w, G.edist w u ≤ t → w ∈ edgeNbhd G t e) →
        (∀ w, G.edist w u' ≤ t → w ∈ edgeNbhd G t e') →
        (∀ b, G.edist b u + m ≤ t → view G x m (σ b) = view G x m b) →
        G.edist y u + (m + 1 : ℕ) ≤ t → view G x (m + 1) (σ y) = view G x (m + 1) y := by
      intro u u' hu' hu hu'N hih hy
      have hyt : G.edist y u + 1 ≤ t :=
        le_trans (by gcongr; exact_mod_cast (show 1 ≤ m + 1 by omega)) hy
      have hyt' : G.edist y u ≤ t := le_trans le_self_add hyt
      have hyN := hu y hyt'
      have hnb : ∀ b, G.Adj y b → G.edist b u + m ≤ t := by
        intro b hb
        calc G.edist b u + m ≤ G.edist y u + 1 + m := by
              gcongr; exact edist_succ_le_of_adj hb
          _ = G.edist y u + (m + 1 : ℕ) := by push_cast; ring
          _ ≤ t := hy
      have hbN : ∀ b, G.Adj y b → b ∈ edgeNbhd G t e := fun b hb =>
        hu b (le_trans (edist_succ_le_of_adj hb) hyt)
      have hσy := hdist y u u' hu' hu hyt'
      refine view_succ_eq (f := σ) (hx y hyN) ⟨fun b hb => ?_, fun a ha b hb h => ?_, fun b' hb' => ?_⟩
        (fun b hb => ?_)
      · exact (hadj y hyN b (hbN b hb)).1 hb
      · exact hσ.injOn (hbN a ha) (hbN b hb) h
      · have hb'N : b' ∈ edgeNbhd G t e' :=
          hu'N b' (le_trans (edist_succ_le_of_adj hb') (le_trans (by gcongr) hyt))
        obtain ⟨b, hbN', rfl⟩ := hσ.surjOn hb'N
        exact ⟨b, (hadj y hyN b hbN').2 hb', rfl⟩
      · exact hih b (hnb b hb)
    rcases hy with hy | hy
    · exact key e.1 e'.1 h1 (fun w hw => mem_edgeNbhd_left hw) (fun w hw => mem_edgeNbhd_left hw)
        (fun b hb => ih b (Or.inl hb)) hy
    · exact key e.2 e'.2 h2 (fun w hw => mem_edgeNbhd_right hw)
        (fun w hw => mem_edgeNbhd_right hw) (fun b hb => ih b (Or.inr hb)) hy

end Transport

/-! ### Views in the crossing -/

section CrossingViews

variable {V α : Type*} {G : SimpleGraph V} {T H T' H' : V}

/-- The position of the two crossed edges `e = (T, H)` and `e' = (T', H')`: both are edges, the
four endpoints are pairwise distinct, and the new edges `TH'`, `T'H` are not edges of `G`. (All
this follows from disjoint `t`-neighbourhoods for `t ≥ 1`, `crossPos_of_disjoint`.) -/
structure CrossPos (G : SimpleGraph V) (T H T' H' : V) : Prop where
  adj : G.Adj T H
  adj' : G.Adj T' H'
  tt : T ≠ T'
  th : T ≠ H'
  ht : H ≠ T'
  hh : H ≠ H'
  nth : ¬ G.Adj T H'
  nht : ¬ G.Adj H T'

variable (h : CrossPos G T H T' H')
include h

lemma CrossPos.adj_T (b : V) :
    (crossing G (T, H) (T', H')).Adj T b ↔ (G.Adj T b ∧ b ≠ H) ∨ b = H' := by
  have := h.adj.ne; have := h.adj'.ne; have := h.tt; have := h.th; have := h.ht; have := h.hh
  simp only [crossing, Sym2.eq_iff]
  grind

lemma CrossPos.adj_H (b : V) :
    (crossing G (T, H) (T', H')).Adj H b ↔ (G.Adj H b ∧ b ≠ T) ∨ b = T' := by
  have := h.adj.ne; have := h.adj'.ne; have := h.tt; have := h.th; have := h.ht; have := h.hh
  simp only [crossing, Sym2.eq_iff]
  grind

lemma CrossPos.adj_T' (b : V) :
    (crossing G (T, H) (T', H')).Adj T' b ↔ (G.Adj T' b ∧ b ≠ H') ∨ b = H := by
  have := h.adj.ne; have := h.adj'.ne; have := h.tt; have := h.th; have := h.ht; have := h.hh
  simp only [crossing, Sym2.eq_iff]
  grind

lemma CrossPos.adj_H' (b : V) :
    (crossing G (T, H) (T', H')).Adj H' b ↔ (G.Adj H' b ∧ b ≠ T') ∨ b = T := by
  have := h.adj.ne; have := h.adj'.ne; have := h.tt; have := h.th; have := h.ht; have := h.hh
  simp only [crossing, Sym2.eq_iff]
  grind

omit h in
/-- Away from the four endpoints, the crossing has the same neighbourhoods. -/
lemma crossing_adj_of_ne {v : V} (hT : v ≠ T) (hH : v ≠ H) (hT' : v ≠ T') (hH' : v ≠ H')
    (b : V) : (crossing G (T, H) (T', H')).Adj v b ↔ G.Adj v b := by
  simp only [crossing, Sym2.eq_iff]
  grind

omit h

/-- If the neighbours of `v` in `C` are those in `G` with `c` replaced by `d`, the swap of `c` and
`d` is a bijection between the neighbourhoods. -/
lemma bijOn_swap_nbr [DecidableEq V] {C : SimpleGraph V} {v c d : V}
    (hC : ∀ b, C.Adj v b ↔ (G.Adj v b ∧ b ≠ c) ∨ b = d) (hc : G.Adj v c) (hd : ¬ G.Adj v d) :
    Set.BijOn (Equiv.swap c d) (G.neighborSet v) (C.neighborSet v) := by
  have hcd : c ≠ d := fun h => hd (h ▸ hc)
  refine Set.InvOn.bijOn (f' := Equiv.swap c d) ⟨fun b _ => by simp, fun b _ => by simp⟩
    (fun b hb => ?_) (fun b hb => ?_)
  · simp only [mem_neighborSet] at hb ⊢
    rw [hC, Equiv.swap_apply_def]
    split_ifs <;> grind
  · simp only [mem_neighborSet] at hb ⊢
    rw [hC] at hb
    rw [Equiv.swap_apply_def]
    split_ifs <;> grind

lemma view_swap [Finite V] [DecidableEq V] {x : V → α} {k : ℕ} {c d : V}
    (hcd : view G x k c = view G x k d) (b : V) :
    view G x k (Equiv.swap c d b) = view G x k b := by
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [h1, hcd]
  · rw [h2, hcd]
  · rfl

/-- One round of the induction behind Proposition 4: if the crossing does not change depth-`k`
views, and `H, H'` (resp. `T, T'`) have the same depth-`k` views in `G`, then the crossing does not
change depth-`(k+1)` views. -/
lemma CrossPos.view_succ [Finite V] (h : CrossPos G T H T' H') {x : V → α} {k : ℕ}
    (hH : view G x k H = view G x k H') (hT : view G x k T = view G x k T')
    (ih : ∀ v, view (crossing G (T, H) (T', H')) x k v = view G x k v) (v : V) :
    view (crossing G (T, H) (T', H')) x (k + 1) v = view G x (k + 1) v := by
  classical
  have hview : ∀ (c d : V), view G x k c = view G x k d → ∀ b, G.Adj v b →
      view (crossing G (T, H) (T', H')) x k (Equiv.swap c d b) = view G x k b :=
    fun c d hcd b _ => by rw [ih, view_swap hcd]
  by_cases hvT : v = T
  · subst hvT
    exact view_succ_eq rfl (bijOn_swap_nbr h.adj_T h.adj h.nth) (hview _ _ hH)
  by_cases hvH : v = H
  · subst hvH
    exact view_succ_eq rfl (bijOn_swap_nbr h.adj_H h.adj.symm h.nht) (hview _ _ hT)
  by_cases hvT' : v = T'
  · subst hvT'
    exact view_succ_eq rfl (bijOn_swap_nbr h.adj_T' h.adj' (fun h' => h.nht h'.symm))
      (hview _ _ hH.symm)
  by_cases hvH' : v = H'
  · subst hvH'
    exact view_succ_eq rfl (bijOn_swap_nbr h.adj_H' h.adj'.symm (fun h' => h.nth h'.symm))
      (hview _ _ hT.symm)
  have hset : (crossing G (T, H) (T', H')).neighborSet v = G.neighborSet v := by
    ext b; exact crossing_adj_of_ne hvT hvH hvT' hvH' b
  exact view_succ_eq (f := id) rfl (hset ▸ Set.bijOn_id _) (fun b _ => ih b)

end CrossingViews

/-! ### Proposition 4, view form -/

section Prop4

variable {V α : Type*} {G : SimpleGraph V} {t : ℕ}

lemma mem_edgeNbhd_of_adj_left {e : V × V} (ht : 1 ≤ t) {w : V} (h : G.Adj w e.1) :
    w ∈ edgeNbhd G t e :=
  Or.inl (by rw [edist_eq_one_iff_adj.2 h]; exact_mod_cast ht)

lemma mem_edgeNbhd_of_adj_right {e : V × V} (ht : 1 ≤ t) {w : V} (h : G.Adj w e.2) :
    w ∈ edgeNbhd G t e :=
  Or.inr (by rw [edist_eq_one_iff_adj.2 h]; exact_mod_cast ht)

lemma fst_mem_edgeNbhd (e : V × V) : e.1 ∈ edgeNbhd G t e := Or.inl (by simp)

lemma snd_mem_edgeNbhd (e : V × V) : e.2 ∈ edgeNbhd G t e := Or.inr (by simp)

/-- Disjoint `t`-neighbourhoods (`t ≥ 1`) of two edges put them in crossing position. -/
lemma crossPos_of_disjoint (ht : 1 ≤ t) {e e' : V × V} (hadj : G.Adj e.1 e.2)
    (hadj' : G.Adj e'.1 e'.2) (hdisj : Disjoint (edgeNbhd G t e) (edgeNbhd G t e')) :
    CrossPos G e.1 e.2 e'.1 e'.2 := by
  have hd := Set.disjoint_left.1 hdisj
  refine ⟨hadj, hadj', fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_,
    fun h => ?_⟩
  · exact hd (fst_mem_edgeNbhd e) (h ▸ fst_mem_edgeNbhd e')
  · exact hd (fst_mem_edgeNbhd e) (h ▸ snd_mem_edgeNbhd e')
  · exact hd (snd_mem_edgeNbhd e) (h ▸ fst_mem_edgeNbhd e')
  · exact hd (snd_mem_edgeNbhd e) (h ▸ snd_mem_edgeNbhd e')
  · exact hd (fst_mem_edgeNbhd e) (mem_edgeNbhd_of_adj_right ht h)
  · exact hd (snd_mem_edgeNbhd e) (mem_edgeNbhd_of_adj_left ht h)

/-- **Proposition 4 of [OPR], anonymous model, view form.** Let `e = (T, H)` and `e' = (T', H')`
be edges of `G` with disjoint `t`-neighbourhoods (`t ≥ 1`), and let `σ : N_t(e) → N_t(e')` be an
isomorphism of the induced subgraphs with `σ T = T'`, `σ H = H'` which preserves the node data `x`
(states and labels). Then every node `v` has the same depth-`k` views, `k ≤ t`, in the crossing
`C(e, e', G)` as in `G`. -/
theorem proposition_4_view [Finite V] (ht : 1 ≤ t) {x : V → α} {e e' : V × V}
    (hadj : G.Adj e.1 e.2) (hadj' : G.Adj e'.1 e'.2)
    (hdisj : Disjoint (edgeNbhd G t e) (edgeNbhd G t e')) {σ : V → V}
    (hσ : Set.BijOn σ (edgeNbhd G t e) (edgeNbhd G t e'))
    (hσadj : ∀ a ∈ edgeNbhd G t e, ∀ b ∈ edgeNbhd G t e, (G.Adj a b ↔ G.Adj (σ a) (σ b)))
    (h1 : σ e.1 = e'.1) (h2 : σ e.2 = e'.2) (hx : ∀ a ∈ edgeNbhd G t e, x (σ a) = x a) :
    ∀ k ≤ t, ∀ v, view (crossing G e e') x k v = view G x k v := by
  have hpos := crossPos_of_disjoint ht hadj hadj' hdisj
  have htr := view_transport hσ hσadj h1 h2 hx
  intro k
  induction k with
  | zero => intro _ _; rfl
  | succ k ih =>
    intro hk v
    have hkt : (k : ℕ∞) ≤ t := by exact_mod_cast (show k ≤ t by omega)
    have hH : view G x k e.2 = view G x k e'.2 := by
      rw [← h2]; exact (htr k e.2 (Or.inr (by simpa using hkt))).symm
    have hT : view G x k e.1 = view G x k e'.1 := by
      rw [← h1]; exact (htr k e.1 (Or.inl (by simpa using hkt))).symm
    exact hpos.view_succ hH hT (ih (by omega)) v

/-- **Proposition 4 of [OPR], anonymous model, acceptance form.** Under the hypotheses of
`proposition_4_view`, if an anonymous `t`-round verifier `D` (a predicate on depth-`t` views)
accepts at every node of `G`, then it accepts at every node of every union `K` of connected
components of the crossing `C(e, e', G)` (in particular of every connected component). -/
theorem proposition_4_accept [Finite V] (ht : 1 ≤ t) {x : V → α} {e e' : V × V}
    (hadj : G.Adj e.1 e.2) (hadj' : G.Adj e'.1 e'.2)
    (hdisj : Disjoint (edgeNbhd G t e) (edgeNbhd G t e')) {σ : V → V}
    (hσ : Set.BijOn σ (edgeNbhd G t e) (edgeNbhd G t e'))
    (hσadj : ∀ a ∈ edgeNbhd G t e, ∀ b ∈ edgeNbhd G t e, (G.Adj a b ↔ G.Adj (σ a) (σ b)))
    (h1 : σ e.1 = e'.1) (h2 : σ e.2 = e'.2) (hx : ∀ a ∈ edgeNbhd G t e, x (σ a) = x a)
    (D : View α t → Prop) (hacc : ∀ v, D (view G x t v)) {K : Set V}
    (hK : ∀ a ∈ K, ∀ b, (crossing G e e').Adj a b → b ∈ K) (w : K) :
    D (view ((crossing G e e').induce K) (x ∘ Subtype.val) t w) := by
  rw [view_induce hK, proposition_4_view ht hadj hadj' hdisj hσ hσadj h1 h2 hx t le_rfl]
  exact hacc w

end Prop4

/-! ### Proposition 4, pigeonhole form -/

section Pigeonhole

variable {V : Type*} {G : SimpleGraph V} {t : ℕ}

/-- The hypotheses of Proposition 4 / item 2 of Theorem 5 with node states `I`: the `r` directed
edges `e i` exist, their `t`-neighbourhoods are pairwise disjoint and have `q` nodes each, and for
all `i, j` there is a state-preserving isomorphism of the induced neighbourhoods
`N_t(e_i) → N_t(e_j)` mapping tail to tail and head to head. (The paper asks for isomorphisms
`N_t(e_1) → N_t(e_i)`; composing them gives ours.) -/
structure StateCrossingHyp {ι : Type*} (G : SimpleGraph V) (I : V → ι) (t r q : ℕ)
    (e : Fin r → V × V) : Prop where
  adj : ∀ i, G.Adj (e i).1 (e i).2
  disjoint : ∀ i j, i ≠ j → Disjoint (edgeNbhd G t (e i)) (edgeNbhd G t (e j))
  card : ∀ i, (edgeNbhd G t (e i)).ncard = q
  iso : ∀ i j, ∃ σ : V → V, Set.BijOn σ (edgeNbhd G t (e i)) (edgeNbhd G t (e j)) ∧
    (∀ a ∈ edgeNbhd G t (e i), ∀ b ∈ edgeNbhd G t (e i), (G.Adj a b ↔ G.Adj (σ a) (σ b))) ∧
    σ (e i).1 = (e j).1 ∧ σ (e i).2 = (e j).2 ∧ ∀ a ∈ edgeNbhd G t (e i), I (σ a) = I a

/-- Without states (`Crossing.lean`'s `CrossingHyp`), the isomorphisms are state preserving. -/
lemma CrossingHyp.toState {r q : ℕ} {e : Fin r → V × V} (h : CrossingHyp G t r q e)
    (I : V → Unit) : StateCrossingHyp G I t r q e :=
  ⟨h.adj, h.disjoint, h.card, fun i j => by
    obtain ⟨σ, h1, h2, h3, h4⟩ := h.iso i j
    exact ⟨σ, h1, h2, h3, h4, fun _ _ => rfl⟩⟩

/-- **Proposition 4 of [OPR], anonymous model.** Let `G` with states `I` contain `r` directed edges
`e i` satisfying the hypotheses of Proposition 4 (`StateCrossingHyp`, `t ≥ 1`), and let `ℓ` be a
labelling with labels from a finite set `L` with `|L|^q < r`. Then there are `i ≠ j` such that every
node has the same depth-`k` views (`k ≤ t`, states and labels attached) in the crossing
`C(e_i, e_j, G)` as in `G`. (The paper's condition `|ℓ| < log r / q` on the label length counts
the possible label strings on a neighbourhood as `2^{q|ℓ|}`, which is right for labels of fixed
length; `|L|^q < r` is the correct pigeonhole condition.) -/
theorem proposition_4_anon [Finite V] {ι Λ : Type*} (ht : 1 ≤ t) {I : V → ι} {r q : ℕ}
    {e : Fin r → V × V} (hc : StateCrossingHyp G I t r q e) (ℓ : V → Λ) (L : Finset Λ)
    (hL : ∀ v, ℓ v ∈ L) (hr : L.card ^ q < r) :
    ∃ i j, i ≠ j ∧ ∀ k ≤ t, ∀ v, view (crossing G (e i) (e j)) (fun u => (I u, ℓ u)) k v =
      view G (fun u => (I u, ℓ u)) k v := by
  classical
  have hr0 : 0 < r := lt_of_le_of_lt (Nat.zero_le _) hr
  set i₀ : Fin r := ⟨0, hr0⟩
  have : Nonempty V := ⟨(e i₀).1⟩
  choose σ hσbij hσadj hσ1 hσ2 hσI using fun i => hc.iso i₀ i
  set N₀ := edgeNbhd G t (e i₀)
  have : Fintype N₀ := Fintype.ofFinite _
  let f : Fin r → (N₀ → L) := fun i a => ⟨ℓ (σ i a), hL _⟩
  have hcard : Fintype.card (N₀ → L) < Fintype.card (Fin r) := by
    rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin, ← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, hc.card]
    exact hr
  obtain ⟨i, j, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hℓ : ∀ a ∈ N₀, ℓ (σ i a) = ℓ (σ j a) := fun a ha =>
    congrArg Subtype.val (congrFun hf ⟨a, ha⟩)
  -- `τ = σ j ∘ (σ i)⁻¹ : N_t(e_i) → N_t(e_j)` preserves states and labels
  set g := Function.invFunOn (σ i) N₀
  have hinv := (hσbij i).invOn_invFunOn
  have hgbij : Set.BijOn g (edgeNbhd G t (e i)) N₀ := (hσbij i).symm hinv.symm
  have hgN : ∀ a ∈ edgeNbhd G t (e i), g a ∈ N₀ := fun a ha => hgbij.mapsTo ha
  have hσg : ∀ a ∈ edgeNbhd G t (e i), σ i (g a) = a := fun a ha => hinv.2 ha
  have hg1 : g (e i).1 = (e i₀).1 := by rw [← hσ1 i]; exact hinv.1 (fst_mem_edgeNbhd _)
  have hg2 : g (e i).2 = (e i₀).2 := by rw [← hσ2 i]; exact hinv.1 (snd_mem_edgeNbhd _)
  refine ⟨i, j, hij, proposition_4_view ht (hc.adj i) (hc.adj j) (hc.disjoint i j hij)
    (σ := σ j ∘ g) ((hσbij j).comp hgbij) (fun a ha b hb => ?_) ?_ ?_ (fun a ha => ?_)⟩
  · simp only [Function.comp_apply]
    rw [← hσadj j _ (hgN a ha) _ (hgN b hb), hσadj i _ (hgN a ha) _ (hgN b hb), hσg a ha,
      hσg b hb]
  · simp [hg1, hσ1]
  · simp [hg2, hσ2]
  · simp only [Function.comp_apply, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [hσI j _ (hgN a ha), ← hσI i _ (hgN a ha), hσg a ha]
    · rw [← hℓ _ (hgN a ha), hσg a ha]

end Pigeonhole

/-! ### Theorem 5 in the anonymous model -/

/-- An *anonymous* `t`-PLS for the predicate `P` on the family `F`, labels in `Λ`: the verifier's
output at `v` is a function `verify` of the depth-`t` view of `v` (states and labels attached),
i.e. of what `v` learns in `t` rounds of anonymous broadcast message passing. Completeness and
soundness on all finite configurations of `F`. -/
structure AnonTPLS (ι Λ : Type) (F P : CProp ι) (t : ℕ) where
  /-- The prover. -/
  prove : ∀ {V : Type}, SimpleGraph V → (V → ι) → V → Λ
  /-- The verifier: `verify W` means that a node with depth-`t` view `W` outputs `true`. -/
  verify : View (ι × Λ) t → Prop
  /-- Completeness. -/
  complete : ∀ {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι), F V G I → P V G I →
    ∀ v, verify (view G (fun u => (I u, prove G I u)) t v)
  /-- Soundness. -/
  sound : ∀ {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι), F V G I →
    ∀ ℓ : V → Λ, (∀ v, verify (view G (fun u => (I u, ℓ u)) t v)) → P V G I

/-- **Theorem 5 of [OPR], anonymous model, exact form.** Let `S` be an anonymous `t`-PLS
(`t ≥ 1`) for `(F, P)` and let `G_s ∈ F` (states `I`) satisfy
1. `P(G_s)`,
2. the hypotheses of Proposition 4 for `r` edges `e i` with `q`-node neighbourhoods
   (`StateCrossingHyp`), and
3. for all `i ≠ j`, some union `K` of connected components of `C(e_i, e_j, G_s)` (e.g. one
   component) lies in `F` and violates `P`.

If the prover's labels on `G_s` come from a finite set `L`, then `r ≤ |L|^q`: at least `r^{1/q}`
distinct labels are needed. -/
theorem theorem_5_anon {ι Λ : Type} {F P : CProp ι} {t : ℕ} (ht : 1 ≤ t) (S : AnonTPLS ι Λ F P t)
    {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι) (hF : F V G I) (hP : P V G I)
    {r q : ℕ} {e : Fin r → V × V} (hc : StateCrossingHyp G I t r q e)
    (h3 : ∀ i j, i ≠ j → ∃ K : Set V, (∀ a ∈ K, ∀ b, (crossing G (e i) (e j)).Adj a b → b ∈ K) ∧
      F K ((crossing G (e i) (e j)).induce K) (I ∘ Subtype.val) ∧
      ¬ P K ((crossing G (e i) (e j)).induce K) (I ∘ Subtype.val))
    (L : Finset Λ) (hL : ∀ v, S.prove G I v ∈ L) : r ≤ L.card ^ q := by
  by_contra hlt
  obtain ⟨i, j, hij, hview⟩ := proposition_4_anon ht hc (S.prove G I) L hL (not_le.1 hlt)
  obtain ⟨K, hK, hFK, hPK⟩ := h3 i j hij
  refine hPK (S.sound _ _ hFK (S.prove G I ∘ Subtype.val) fun w => ?_)
  have := view_induce hK (fun u => (I u, S.prove G I u)) t w
  simp only [Function.comp_def] at this ⊢
  rw [this, hview t le_rfl]
  exact S.complete G I hF hP w

/-- **Theorem 5 of [OPR], anonymous model, label size.** With labels bit strings of length
`≤ m` on `G_s`, `r ≤ 2^{(m+1) q}`, i.e. `m + 1 ≥ log₂ r / q`: the label size is
`Ω(log r / q)`. -/
theorem theorem_5_anon_length {ι : Type} {F P : CProp ι} {t : ℕ} (ht : 1 ≤ t)
    (S : AnonTPLS ι (List Bool) F P t) {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι)
    (hF : F V G I) (hP : P V G I) {r q : ℕ} {e : Fin r → V × V}
    (hc : StateCrossingHyp G I t r q e)
    (h3 : ∀ i j, i ≠ j → ∃ K : Set V, (∀ a ∈ K, ∀ b, (crossing G (e i) (e j)).Adj a b → b ∈ K) ∧
      F K ((crossing G (e i) (e j)).induce K) (I ∘ Subtype.val) ∧
      ¬ P K ((crossing G (e i) (e j)).induce K) (I ∘ Subtype.val))
    (m : ℕ) (hm : ∀ v, (S.prove G I v).length ≤ m) : r ≤ 2 ^ ((m + 1) * q) := by
  have h := theorem_5_anon ht S G I hF hP hc h3 (bitStrings m) fun v => mem_bitStrings (hm v)
  calc r ≤ (bitStrings m).card ^ q := h
    _ ≤ (2 ^ (m + 1)) ^ q := Nat.pow_le_pow_left (le_trans (card_bitStrings m) (Nat.sub_le _ _)) _
    _ = 2 ^ ((m + 1) * q) := by rw [← pow_mul]

/-! ### Non-vacuity: the disjoint triangles -/

/-- The hypotheses of Proposition 4 are satisfiable: the disjoint triangles of `Crossing.lean`. -/
lemma triangles_stateHyp (r : ℕ) :
    StateCrossingHyp (triangles r) (fun _ => ()) 2 r 3 (triEdge r) :=
  (triangles_hyp r).toState _

/-- In the anonymous model the counterexample of `Crossing.lean` disappears: for `i ≠ j`, every node
of the crossing of the triangles `i` and `j` (a 6-cycle plus the other triangles) has the same
depth-`k` views, `k ≤ 2`, as in the disjoint triangles, so no anonymous 2-round verifier tells a
triangle from a 6-cycle. -/
theorem triangles_view_eq {r : ℕ} {i j : Fin r} (hij : i ≠ j) :
    ∀ k ≤ 2, ∀ v, view (triCross i j) (fun _ => ()) k v = view (triangles r) (fun _ => ()) k v := by
  have hc := triangles_stateHyp r
  obtain ⟨σ, h1, h2, h3, h4, -⟩ := hc.iso i j
  exact proposition_4_view (by norm_num) (hc.adj i) (hc.adj j) (hc.disjoint i j hij) h1 h2 h3 h4
    (fun _ _ => rfl)

end Podc.SpaceTimeVerification
