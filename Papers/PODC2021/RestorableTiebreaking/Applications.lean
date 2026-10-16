import Papers.PODC2021.RestorableTiebreaking.Existence

/-!
# Applications (Section 4): preservers, labels, additive spanners

Bodwin–Parter, PODC 2021, Section 4. We formalize the *correctness* parts of the applications and
the parts of the size bounds that do not depend on external results:

* `overlay π S f` — the union of all selected paths `π(s, v | F)`, `s ∈ S`, `v ∈ V`, `|F| ≤ f`.
* `overlay_isFTPreserver` — it is an `f`-FT `S × V` preserver (any `f`-RPTS).
* `theorem31_correct` — **Theorem 31 (correctness)**: if `π` is an `(f+1)`-restorable
  `(f+1)`-RPTS, the `f`-fault overlay is an `(f+1)`-FT `S × S` preserver.
  `theorem31_of_theorem26` turns any size bound for overlays of consistent stable `f`-RPTSes
  (Theorem 26, cited from [9] and not proved in the paper) into the size bound of Theorem 31.
* `card_overlay_zero_le` — for consistent `π`, the non-faulty overlay from `S` has at most
  `|S| (n - 1)` edges (a union of `|S|` trees); `theorem31_f0` — the `f = 0` case of Theorem 31,
  unconditional: a 1-FT `S × S` preserver with at most `|S| (n - 1)` edges.
* `theorem30_correct` — **Theorem 30 (correctness)**: storing the `f`-fault overlay from `s` as
  the label of `s` gives an `(f+1)`-FT exact distance labeling; `theorem30` — for `f = 0` each
  label has at most `n - 1` edges. The `f = 0` case is also the correctness of Algorithm 1
  (Theorem 29): `T_{s₁} ∪ T_{s₂}` contains a replacement path for every single failing edge.
* `lemma32_correct` — **Lemma 32 (correctness)**: clustering + an `f`-FT subset preserver on the
  cluster centers is an `f`-FT `+4` additive spanner.
* `theorem33_exponent` — the exponent arithmetic of Theorem 33.
-/

open Finset SimpleGraph SimpleGraph.Walk

set_option linter.unusedSectionVars false

namespace RestorableTiebreaking

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- Definition 4: `H` is an `f`-FT `S × T` (distance) preserver of `G`. -/
def IsFTPreserver (G H : SimpleGraph V) (S T : Set V) (f : ℕ) : Prop :=
  H ≤ G ∧ ∀ F : Finset (Sym2 V), #F ≤ f → ∀ s ∈ S, ∀ t ∈ T,
    (H.deleteEdges F).edist s t = (G.deleteEdges F).edist s t

/-- Definition 6: `H` is an `f`-FT `+k` additive spanner of `G` for the pairs in `S × S`. -/
def IsFTAdditiveSpanner (G H : SimpleGraph V) (S : Set V) (f k : ℕ) : Prop :=
  H ≤ G ∧ ∀ F : Finset (Sym2 V), #F ≤ f → ∀ s ∈ S, ∀ t ∈ S,
    (H.deleteEdges F).edist s t ≤ (G.deleteEdges F).edist s t + k

/-- A walk all of whose darts are edges of `H'` bounds `d_{H'}`. -/
lemma edist_le_of_darts {G' H' : SimpleGraph V} {u v : V} (p : G'.Walk u v)
    (h : ∀ d ∈ p.darts, H'.Adj d.fst d.snd) : H'.edist u v ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c hab q ih =>
    have h1 : H'.Adj a b := h ⟨(a, b), hab⟩ (by simp)
    have h2 := ih fun d hd => h d (by simp [hd])
    calc H'.edist a c ≤ H'.edist a b + H'.edist b c := H'.edist_triangle
      _ ≤ 1 + q.length := add_le_add (edist_eq_one_iff_adj.mpr h1).le h2
      _ = (cons hab q).length := by rw [length_cons]; push_cast; ring

/-- Lower bound: subgraphs only increase distances. -/
lemma edist_deleteEdges_le_of_le {H : SimpleGraph V} (hHG : H ≤ G) (F : Set (Sym2 V)) (u v : V) :
    (G.deleteEdges F).edist u v ≤ (H.deleteEdges F).edist u v :=
  edist_anti (deleteEdges_mono hHG)

/-! ### Overlays -/

/-- The edges used by the selected paths `π(s, v | F)`, `s ∈ S`, `v ∈ V`, `|F| ≤ f`. -/
def overlayEdges (π : Scheme G) (S : Set V) (f : ℕ) : Set (Sym2 V) :=
  {e | ∃ F : Finset (Sym2 V), #F ≤ f ∧ ∃ s ∈ S, ∃ v p, π F s v = some p ∧ e ∈ p.edges}

/-- The overlay of the selected `S × V` replacement paths under `≤ f` faults. -/
def overlay (π : Scheme G) (S : Set V) (f : ℕ) : SimpleGraph V :=
  fromEdgeSet (overlayEdges π S f)

lemma overlay_le (π : Scheme G) (S : Set V) (f : ℕ) : overlay π S f ≤ G := by
  rintro u v ⟨⟨F, -, s, -, w, p, -, he⟩, hne⟩
  exact p.edges_subset_edgeSet he

lemma overlay_mono {π : Scheme G} {S S' : Set V} (h : S ⊆ S') (f : ℕ) :
    overlay π S f ≤ overlay π S' f := by
  rintro u v ⟨⟨F, hF, s, hs, w, p, hp, he⟩, hne⟩
  exact ⟨⟨F, hF, s, h hs, w, p, hp, he⟩, hne⟩

/-- A walk of `G` whose edges are selected edges and avoid `F` is a walk of `overlay \ F`. -/
lemma edist_overlay_le {π : Scheme G} {S : Set V} {f : ℕ} {F : Set (Sym2 V)} {u v : V}
    (p : G.Walk u v) (hp : ∀ e ∈ p.edges, e ∈ overlayEdges π S f) (hF : p.Avoids F) :
    ((overlay π S f).deleteEdges F).edist u v ≤ p.length := by
  refine edist_le_of_darts p fun d hd => ?_
  have he : d.edge ∈ p.edges := List.mem_map_of_mem hd
  rw [deleteEdges_adj]
  exact ⟨⟨hp _ he, d.adj.ne⟩, hF _ he⟩

lemma mem_overlayEdges {π : Scheme G} {S : Set V} {f : ℕ} {F : Finset (Sym2 V)} (hF : #F ≤ f)
    {s v : V} (hs : s ∈ S) {p : G.Walk s v} (hp : π F s v = some p) :
    ∀ e ∈ p.edges, e ∈ overlayEdges π S f :=
  fun _ he => ⟨F, hF, s, hs, v, p, hp, he⟩

/-- The overlay of an `f`-RPTS is an `f`-FT `S × V` preserver. -/
theorem overlay_isFTPreserver {π : Scheme G} {f : ℕ} (hπ : IsRPTS G f π) (S : Set V) :
    IsFTPreserver G (overlay π S f) S Set.univ f := by
  refine ⟨overlay_le π S f, fun F hF s hs t _ => le_antisymm ?_
    (edist_deleteEdges_le_of_le (overlay_le π S f) _ _ _)⟩
  by_cases hst : (G.deleteEdges F).Reachable s t
  · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp ((hπ F hF).2 s t hst)
    have hsh := (hπ F hF).1 s t p hp
    rw [← hsh.2]
    exact edist_overlay_le p (mem_overlayEdges hF hs hp) hsh.1
  · rw [edist_eq_top_of_not_reachable hst]; exact le_top

/-- **Theorem 31 of [Bodwin–Parter] (correctness).** If `π` is an `(f+1)`-RPTS that is
`(f+1)`-restorable, then overlaying all `S × V` replacement paths selected by `π` under `≤ f`
faults gives an `(f+1)`-FT `S × S` preserver. -/
theorem theorem31_correct {π : Scheme G} {f : ℕ} (hπ : IsRPTS G (f + 1) π)
    (hres : IsRestorable G (f + 1) π) (S : Set V) :
    IsFTPreserver G (overlay π S f) S S (f + 1) := by
  refine ⟨overlay_le π S f, fun F hF s hs t ht => le_antisymm ?_
    (edist_deleteEdges_le_of_le (overlay_le π S f) _ _ _)⟩
  by_cases hst : (G.deleteEdges F).Reachable s t
  · rcases F.eq_empty_or_nonempty with rfl | hne
    · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp ((hπ ∅ (by simp)).2 s t hst)
      have hsh := (hπ ∅ (by simp)).1 s t p hp
      rw [← hsh.2]
      exact edist_overlay_le p (mem_overlayEdges (by simp) hs hp) hsh.1
    · obtain ⟨F', hF', x, p, q, hp, hq, hW⟩ := hres F hF hne s t hst
      have hF'f : #F' ≤ f := by have := card_lt_card hF'; omega
      rw [← hW.2]
      refine edist_overlay_le _ (fun e he => ?_) hW.1
      rw [edges_append, List.mem_append, edges_reverse, List.mem_reverse] at he
      rcases he with he | he
      · exact mem_overlayEdges hF'f hs hp e he
      · exact mem_overlayEdges hF'f ht hq e he
  · rw [edist_eq_top_of_not_reachable hst]; exact le_top

/-- **Theorem 31 of [Bodwin–Parter]** from Theorem 26: if the `f`-fault `S × V` overlay of every
consistent, stable `f`-RPTS has at most `g` edges (Theorem 26, a result of [9] that the paper
cites with a proof sketch), then every finite graph has an `(f+1)`-FT `S × S` preserver with at
most `g` edges. -/
theorem theorem31_of_theorem26 [Fintype V] (G : SimpleGraph V) (S : Set V) (f g : ℕ)
    (thm26 : ∀ π : Scheme G, IsRPTS G f π → IsConsistent G f π → IsStable G f π →
      (overlayEdges π S f ∩ G.edgeSet).ncard ≤ g) :
    ∃ H : SimpleGraph V, IsFTPreserver G H S S (f + 1) ∧ H.edgeSet.ncard ≤ g := by
  let : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  set π := atwScheme G (rOf (detRho (Fintype.equivFin (Sym2 V))))
  obtain ⟨h1, h2, h3, h4⟩ := theorem19 (theorem23 (G := G) (Fintype.equivFin (Sym2 V)) (f + 1))
  refine ⟨overlay π S f, theorem31_correct h1 h4 S, ?_⟩
  refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (thm26 π ?_ ?_ ?_)
  · intro e he
    refine ⟨?_, (overlay_le π S f) |> fun h => edgeSet_mono h he⟩
    rw [overlay, edgeSet_fromEdgeSet] at he
    exact he.1
  · exact fun F hF => h1 F (by omega)
  · exact fun F hF => h3 F (by omega)
  · exact fun F hF => h2 F (by omega)

/-! ### Non-faulty overlays of consistent schemes are unions of trees -/

/-- For a consistent scheme, every edge of a selected path `π(s, v)` is the last edge of the
selected path `π(s, b)` to its far endpoint `b`. -/
lemma exists_last_edge {π : Scheme G} {f : ℕ} (hc : IsConsistent G f π) {F : Finset (Sym2 V)}
    (hF : #F ≤ f) {s v : V} {p : G.Walk s v} (hp : π F s v = some p) {e : Sym2 V}
    (he : e ∈ p.edges) :
    ∃ (b : V) (pb : G.Walk s b), π F s b = some pb ∧ ¬ pb.Nil ∧ e = s(pb.penultimate, b) := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  obtain ⟨p₁, p₂, rfl⟩ := exists_eq_append_cons_of_mem_darts hd
  refine ⟨d.snd, p₁.concat d.adj, ?_, by simp [concat_eq_append], ?_⟩
  · refine hc F hF s v _ hp s d.snd nil (p₁.concat d.adj) p₂ ?_
    rw [concat_eq_append, nil_append, ← append_assoc]; rfl
  · rw [penultimate_concat]; rfl

/-- For a consistent scheme, the overlay of the non-faulty selected paths from the sources `S`
has at most `|S| (n - 1)` edges (it is a union of `|S|` shortest-path trees). -/
theorem card_overlay_zero_le [Fintype V] {π : Scheme G} {f : ℕ} (hπ : IsRPTS G f π)
    (hc : IsConsistent G f π) (S : Finset V) : (overlayEdges π S 0).ncard ≤ #S * (Fintype.card V - 1) := by
  classical
  let g : V × V → Sym2 V := fun sb =>
    match π ∅ sb.1 sb.2 with
    | some pb => s(pb.penultimate, sb.2)
    | none => s(sb.1, sb.1)
  let D : Finset (V × V) := (S ×ˢ univ).filter fun sb => sb.1 ≠ sb.2
  have hsub : overlayEdges π S 0 ⊆ (D.image g : Set (Sym2 V)) := by
    rintro e ⟨F, hF, s, hs, v, p, hp, he⟩
    have hF0 : F = ∅ := card_eq_zero.mp (Nat.le_zero.mp hF)
    subst hF0
    obtain ⟨b, pb, hpb, hnil, rfl⟩ := exists_last_edge hc (by simp) hp he
    refine mem_coe.mpr (mem_image.mpr ⟨(s, b), ?_, ?_⟩)
    · simp only [D, mem_filter, mem_product, mem_univ, and_true]
      refine ⟨by exact_mod_cast hs, fun hsb => ?_⟩
      subst hsb
      exact hnil (((hπ ∅ (by simp)).1 _ _ _ hpb).nil_iff ▸ Nil.nil)
    · simp [g, hpb]
  calc (overlayEdges π S 0).ncard ≤ (D.image g : Set (Sym2 V)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = #(D.image g) := Set.ncard_coe_finset _
    _ ≤ #D := card_image_le
    _ = #S * (Fintype.card V - 1) := by
        simp only [D]
        rw [show (S ×ˢ univ).filter (fun sb : V × V => sb.1 ≠ sb.2) =
            S.biUnion (fun s => ({s} : Finset V) ×ˢ (univ.erase s)) from ?_]
        · rw [card_biUnion]
          · simp [card_erase_of_mem]
          · intro a _ b _ hab
            simp only [Function.onFun]
            rw [Finset.disjoint_left]
            intro x hx hx'
            simp only [mem_product, mem_singleton] at hx hx'
            exact hab (hx.1.symm.trans hx'.1)
        · ext ⟨a, b⟩
          simp [eq_comm, and_comm]

/-- The ATW scheme used for all applications. -/
noncomputable def canonScheme [Fintype V] (G : SimpleGraph V) : Scheme G :=
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  atwScheme G (rOf (detRho (Fintype.equivFin (Sym2 V))))

lemma canonScheme_spec [Fintype V] (G : SimpleGraph V) (f : ℕ) :
    IsRPTS G f (canonScheme G) ∧ IsStable G f (canonScheme G) ∧
      IsConsistent G f (canonScheme G) ∧ IsRestorable G f (canonScheme G) :=
  letI : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  theorem19 (theorem23 (G := G) (Fintype.equivFin (Sym2 V)) f)

lemma ncard_edgeSet_overlay_le [Fintype V] (π : Scheme G) (S : Set V) (f : ℕ) :
    (overlay π S f).edgeSet.ncard ≤ (overlayEdges π S f).ncard := by
  refine Set.ncard_le_ncard (fun e he => ?_) (Set.toFinite _)
  rw [overlay, edgeSet_fromEdgeSet] at he
  exact he.1

/-- **Theorem 31 of [Bodwin–Parter], case `f = 0`** (unconditional): every finite graph has a
1-FT `S × S` distance preserver with at most `|S| (n - 1)` edges, namely the union of the
shortest-path trees from `S` selected by a 1-restorable consistent scheme. -/
theorem theorem31_f0 [Fintype V] (G : SimpleGraph V) (S : Finset V) :
    ∃ H : SimpleGraph V, IsFTPreserver G H S S 1 ∧
      H.edgeSet.ncard ≤ #S * (Fintype.card V - 1) := by
  obtain ⟨h1, -, h3, h4⟩ := canonScheme_spec G 1
  refine ⟨overlay (canonScheme G) S 0, theorem31_correct h1 h4 _, ?_⟩
  exact (ncard_edgeSet_overlay_le _ _ _).trans (card_overlay_zero_le h1 h3 S)

lemma overlayEdges_pair (π : Scheme G) (s t : V) (f : ℕ) :
    overlayEdges π {s, t} f = overlayEdges π {s} f ∪ overlayEdges π {t} f := by
  ext e
  simp only [overlayEdges, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union,
    Set.mem_ofPred_eq, exists_eq_or_imp, exists_eq_left]
  constructor
  · rintro ⟨F, hF, h | h⟩
    · exact .inl ⟨F, hF, h⟩
    · exact .inr ⟨F, hF, h⟩
  · rintro (⟨F, hF, h⟩ | ⟨F, hF, h⟩)
    · exact ⟨F, hF, .inl h⟩
    · exact ⟨F, hF, .inr h⟩

/-- Correctness of the labels of Theorem 30: if `π` is an `(f+1)`-restorable `(f+1)`-RPTS and the
label of `s` is the edge set of the `f`-fault overlay from `s`, then for every fault set `F` with
`|F| ≤ f + 1`, `d_{G \ F}(s, t)` is the distance from `s` to `t` in the graph formed by the edges
of the two labels minus `F`. -/
theorem theorem30_correct {π : Scheme G} {f : ℕ} (hπ : IsRPTS G (f + 1) π)
    (hres : IsRestorable G (f + 1) π) (F : Finset (Sym2 V)) (hF : #F ≤ f + 1) (s t : V) :
    ((fromEdgeSet (overlayEdges π {s} f ∪ overlayEdges π {t} f)).deleteEdges F).edist s t =
      (G.deleteEdges F).edist s t := by
  rw [← overlayEdges_pair]
  exact (theorem31_correct hπ hres {s, t}).2 F hF s (by simp) t (by simp)

/-- **Theorem 30 of [Bodwin–Parter]** (correctness for every `f`, size for `f = 0`). Every finite
graph has an `(f+1)`-FT exact distance labeling in which the label of a vertex is a set of edges
and `d_{G \ F}(s, t)` is computed from the labels of `s, t` and from `F` alone; for `f = 0` every
label has at most `n - 1` edges (i.e. `O(n log n)` bits). For `f ≥ 1` the label size is the size
of an `f`-FT `{s} × V` overlay, bounded in the paper by the cited Theorem 26. -/
theorem theorem30 [Fintype V] (G : SimpleGraph V) (f : ℕ) :
    ∃ L : V → Set (Sym2 V),
      (∀ F : Finset (Sym2 V), #F ≤ f + 1 → ∀ s t,
        ((fromEdgeSet (L s ∪ L t)).deleteEdges F).edist s t = (G.deleteEdges F).edist s t) ∧
      (f = 0 → ∀ s, (L s).ncard ≤ Fintype.card V - 1) := by
  obtain ⟨h1, -, h3, h4⟩ := canonScheme_spec G (f + 1)
  refine ⟨fun s => overlayEdges (canonScheme G) {s} f, fun F hF s t => theorem30_correct h1 h4 F hF s t,
    ?_⟩
  rintro rfl s
  have := card_overlay_zero_le h1 h3 {s}
  simpa using this

/-- Correctness of Algorithm 1 (Theorem 29): with `T_s` the tree of non-faulty selected paths
from `s` (for a 1-restorable 1-RPTS), `T_{s₁} ∪ T_{s₂}` contains a shortest `s₁ ⇝ s₂`
replacement path for every failing edge `e`. -/
theorem theorem29_correct {π : Scheme G} (hπ : IsRPTS G 1 π) (hres : IsRestorable G 1 π)
    (s₁ s₂ : V) (e : Sym2 V) :
    ((fromEdgeSet (overlayEdges π {s₁} 0 ∪ overlayEdges π {s₂} 0)).deleteEdges {e}).edist s₁ s₂ =
      (G.deleteEdges {e}).edist s₁ s₂ := by
  simpa using theorem30_correct hπ hres {e} (by simp) s₁ s₂

end RestorableTiebreaking
