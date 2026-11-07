import Papers.PODC2013.SourceDetectionCongest.TopK

/-!
# Hop distances, the lists `L_v^{(d)}` and Lemma 4.5

The communication graph is an arbitrary relation `E : V → V → Prop` on a finite set of nodes `V`
(`E u v`: `u` can send to `v`). For an undirected graph `G` this is `G.Adj`
(`hd_adj_eq_edist` below identifies the hop distance with Mathlib's `SimpleGraph.edist`); for a
directed graph it gives Section 4.4 of the paper. Node identifiers are the elements of `V`,
which carries a linear order (the identifier order used for tie-breaking).

`hd E s v` is the number of hops of a shortest `E`-walk from `s` to `v` (`⊤` if there is none).
`Lspec E S d v` is the paper's `L_v^{(d)}`: the set of pairs `(hd(s,v), s)`, `s ∈ S`,
`hd(s,v) ≤ d`, in `ℕ ×ₗ V` (lexicographic order).
-/

namespace Podc.SourceDetectionCongest

open Finset

variable {V : Type*}

-- CSLib candidate: hop distance along an arbitrary relation, with the bridge `hd_adj_eq_edist`.
/-- `Reach E n s v`: there is a walk with exactly `n` hops along `E` from `s` to `v`. -/
def Reach (E : V → V → Prop) : ℕ → V → V → Prop
  | 0, s, v => s = v
  | n + 1, s, v => ∃ u, Reach E n s u ∧ E u v

open Classical in
/-- Hop distance from `s` to `v` along `E` (`⊤` if `v` is not reachable from `s`). -/
noncomputable def hd (E : V → V → Prop) (s v : V) : ℕ∞ :=
  if h : ∃ n, Reach E n s v then (Nat.find h : ℕ∞) else ⊤

variable {E : V → V → Prop} {s u v : V} {n : ℕ}

lemma hd_le_of_reach (h : Reach E n s v) : hd E s v ≤ n := by
  classical
  have h' : ∃ n, Reach E n s v := ⟨n, h⟩
  simp only [hd, h', ↓reduceDIte]
  exact_mod_cast Nat.find_min' h' h

lemma reach_of_hd_eq (h : hd E s v = n) : Reach E n s v := by
  classical
  unfold hd at h
  split_ifs at h with h'
  · have := Nat.find_spec h'
    rw [Nat.cast_inj] at h
    rwa [h] at this
  · exact absurd h (ENat.top_ne_natCast n)

@[simp] lemma hd_self : hd E s s = 0 :=
  le_antisymm (hd_le_of_reach (n := 0) rfl) bot_le

lemma hd_eq_zero : hd E s v = 0 ↔ s = v := by
  refine ⟨fun h => ?_, fun h => h ▸ hd_self⟩
  exact reach_of_hd_eq (n := 0) (by simpa using h)

lemma hd_le_succ (h : E u v) : hd E s v ≤ hd E s u + 1 := by
  generalize hm : hd E s u = m
  induction m using ENat.recTopCoe with
  | top => simp
  | coe m =>
    exact_mod_cast hd_le_of_reach (E := E) (n := m + 1) ⟨u, reach_of_hd_eq hm, h⟩

lemma exists_pred_of_hd_eq_succ (h : hd E s v = (n + 1 : ℕ)) :
    ∃ u, E u v ∧ hd E s u = n := by
  obtain ⟨u, hu, huv⟩ := reach_of_hd_eq h
  refine ⟨u, huv, le_antisymm (hd_le_of_reach hu) ?_⟩
  have := hd_le_succ (s := s) huv
  rw [h] at this
  generalize hm : hd E s u = m at this
  induction m using ENat.recTopCoe with
  | top => simp
  | coe m =>
    have : n + 1 ≤ m + 1 := by exact_mod_cast this
    exact_mod_cast (by omega : n ≤ m)

/-- For a simple graph, `n`-hop reachability is the existence of a walk of length `n`. -/
lemma reach_adj_iff (G : SimpleGraph V) :
    ∀ n s v, Reach G.Adj n s v ↔ ∃ p : G.Walk v s, p.length = n
  | 0, s, v => by
      constructor
      · rintro rfl; exact ⟨.nil, rfl⟩
      · rintro ⟨p, hp⟩; exact (SimpleGraph.Walk.eq_of_length_eq_zero hp).symm
  | n + 1, s, v => by
      constructor
      · rintro ⟨u, hu, huv⟩
        obtain ⟨p, hp⟩ := (reach_adj_iff G n s u).1 hu
        exact ⟨.cons huv.symm p, by simp [hp]⟩
      · rintro ⟨p, hp⟩
        cases p with
        | nil => simp at hp
        | cons h q =>
          exact ⟨_, (reach_adj_iff G n s _).2 ⟨q, by simpa using hp⟩, h.symm⟩

/-- For a simple graph the hop distance is Mathlib's extended graph distance. -/
lemma hd_adj_eq_edist (G : SimpleGraph V) (s v : V) : hd G.Adj s v = G.edist s v := by
  apply le_antisymm
  · by_cases h : G.edist s v = ⊤
    · simp [h]
    · obtain ⟨p, hp⟩ := SimpleGraph.Reachable.exists_walk_length_eq_edist
        (SimpleGraph.edist_ne_top_iff_reachable.1 h)
      rw [← hp]
      exact hd_le_of_reach ((reach_adj_iff G _ s v).2 ⟨p.reverse, by simp⟩)
  · by_cases h : hd G.Adj s v = ⊤
    · simp [h]
    · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 h
      obtain ⟨p, hp⟩ := (reach_adj_iff G m s v).1 (reach_of_hd_eq hm.symm)
      rw [← hm, ← hp, ← SimpleGraph.Walk.length_reverse]
      exact SimpleGraph.edist_le _

section Lists

variable [LinearOrder V]

variable (E) in
/-- The paper's `L_v^{(d)}` (Definitions 1.1 / 4.1): the pairs `(hd(s,v), s)` for the sources
`s ∈ S` within `d` hops, ordered lexicographically (distance first, then identifier). -/
noncomputable def Lspec (S : Finset V) (d : ℕ) (v : V) : Finset (ℕ ×ₗ V) :=
  (S.filter fun s => hd E s v ≤ d).image fun s => toLex ((hd E s v).toNat, s)

variable {S : Finset V} {d k m : ℕ} {w : V}

lemma mem_Lspec : toLex (m, s) ∈ Lspec E S d v ↔ s ∈ S ∧ hd E s v = m ∧ m ≤ d := by
  simp only [Lspec, mem_image, mem_filter]
  constructor
  · rintro ⟨s', ⟨hs', hd'⟩, heq⟩
    simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at heq
    obtain ⟨h1, rfl⟩ := heq
    have hfin : hd E s' v ≠ ⊤ := ne_top_of_le_ne_top (by simp) hd'
    have hm : hd E s' v = m := by rw [← h1]; exact (ENat.natCast_toNat hfin).symm
    refine ⟨hs', hm, ?_⟩
    rw [hm] at hd'; exact_mod_cast hd'
  · rintro ⟨hs, hm, hmd⟩
    exact ⟨s, ⟨hs, by rw [hm]; exact_mod_cast hmd⟩, by simp [hm]⟩

lemma Lspec_mono {d d' : ℕ} (h : d ≤ d') : Lspec E S d v ⊆ Lspec E S d' v := by
  intro x hx
  obtain ⟨⟨m, s⟩, rfl⟩ := toLex.surjective x
  rw [mem_Lspec] at *
  exact ⟨hx.1, hx.2.1, hx.2.2.trans h⟩

/-- Core of Lemma 4.5: if `(m + 1, s)` is among the `k` closest sources of `v` within `d + 1`
hops and `w` is a predecessor of `v` with `hd(s, w) = m`, then `(m, s)` is among the `k` closest
sources of `w` within `d` hops. (Any predecessor on a shortest path works, not just one.) -/
lemma mem_topk_Lspec_pred (hx : toLex (m + 1, s) ∈ topk k (Lspec E S (d + 1) v))
    (hw : E w v) (hws : hd E s w = m) : toLex (m, s) ∈ topk k (Lspec E S d w) := by
  rw [mem_topk] at hx ⊢
  have hxL := mem_Lspec.1 hx.1
  refine ⟨mem_Lspec.2 ⟨hxL.1, hws, by omega⟩, lt_of_le_of_lt ?_ hx.2⟩
  -- map `(hd(s',w), s') ↦ (hd(s',v), s')`
  refine card_le_card_of_injOn
    (fun y => toLex ((hd E (ofLex y).2 v).toNat, (ofLex y).2)) ?_ ?_
  · intro y hy
    obtain ⟨⟨m', s'⟩, rfl⟩ := toLex.surjective y
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Lspec, ofLex_toLex] at hy ⊢
    obtain ⟨⟨hs', hm', hm'd⟩, hlt⟩ := hy
    have hle : hd E s' v ≤ (m' + 1 : ℕ) := by
      have := hd_le_succ (s := s') hw; rw [hm'] at this; exact_mod_cast this
    have hfin : hd E s' v ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
    have hle' : (hd E s' v).toNat ≤ m' + 1 := by
      rw [← ENat.natCast_le_natCast, ENat.natCast_toNat hfin]; exact hle
    refine ⟨⟨hs', ENat.natCast_toNat hfin |>.symm, by omega⟩, ?_⟩
    rw [Prod.Lex.toLex_lt_toLex] at hlt ⊢
    simp only at hlt ⊢
    rcases hlt with h | ⟨h1, h2⟩
    · left; omega
    · rcases Nat.lt_or_ge (hd E s' v).toNat (m + 1) with h3 | h3
      · exact Or.inl h3
      · exact Or.inr ⟨by omega, h2⟩
  · intro y hy y' hy' heq
    obtain ⟨⟨m', s'⟩, rfl⟩ := toLex.surjective y
    obtain ⟨⟨m'', s''⟩, rfl⟩ := toLex.surjective y'
    simp only [coe_filter, Set.mem_ofPred_eq, mem_Lspec, ofLex_toLex,
      EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq] at hy hy' heq
    obtain ⟨-, rfl⟩ := heq
    have : (m' : ℕ∞) = m'' := hy.1.2.1.symm.trans hy'.1.2.1
    simp only [Nat.cast_inj] at this
    rw [this]

/-- **Lemma 4.5.** `top_k(L_v^{(d)}) ⊆ L_v^{(0)} ∪ {(hd(w,s) + 1, s) | (hd(w,s), s) ∈
top_k(L_w^{(d-1)}), w → v}`. (The paper assumes `d, k ≥ 1`; neither is needed.) -/
theorem lemma_4_5 [Fintype V] [DecidableRel E] (d k : ℕ) (v : V) :
    topk k (Lspec E S d v) ⊆ Lspec E S 0 v ∪ (univ.filter (E · v)).biUnion fun w =>
      (topk k (Lspec E S (d - 1) w)).image fun x => toLex ((ofLex x).1 + 1, (ofLex x).2) := by
  intro x hx
  obtain ⟨⟨m, s⟩, rfl⟩ := toLex.surjective x
  have hL := mem_Lspec.1 (topk_subset hx)
  rcases m with _ | m
  · exact mem_union_left _ (mem_Lspec.2 ⟨hL.1, hL.2.1, le_rfl⟩)
  · obtain ⟨w, hw, hws⟩ := exists_pred_of_hd_eq_succ hL.2.1
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    refine mem_union_right _ (mem_biUnion.2 ⟨w, by simpa using hw, mem_image.2
      ⟨toLex (m, s), ?_, by simp⟩⟩)
    simpa using mem_topk_Lspec_pred hx hw hws

end Lists

end Podc.SourceDetectionCongest
