import Papers.PODC2015.AlgebraicCongestedClique.Tiles

/-!
# 4-cycle detection: combinatorics (Section 3.1 of Censor-Hillel et al., PODC 2015)

* `HasFourCycle G`: `G` contains a cycle of length 4.
* `hasFourCycle_iff`: there is a 4-cycle iff `|P(x,∗,z)| ≥ 2` for some `x ≠ z`.
* `exists_of_card_walksFrom`: Phase 1 — if `|P(x,∗,∗)| ≥ 2n − 1` there is a 4-cycle.
* `chunk`: the partitions `N_A(y,a)` / `N_B(y,b)` of a neighbourhood into parts of size `≤ 8`.
* `lemma_13`: the sets `W(b)` partition `P(∗,∗,∗)` and `|W(b)| ≤ 64 n`.
-/

namespace Podc.AlgebraicCongestedClique

open Finset SimpleGraph

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- `G` contains a 4-cycle. -/
def HasFourCycle : Prop := ∃ (v : Fin n) (c : G.Walk v v), c.IsCycle ∧ c.length = 4

/-- `P(x, ∗, z)`: the middle vertices of the 2-walks from `x` to `z`. -/
def commonNbrs (x z : Fin n) : Finset (Fin n) := univ.filter fun y => G.Adj x y ∧ G.Adj y z

/-- `P(∗, ∗, ∗)`: all 2-walks `(x, y, z)` (`{x,y}, {y,z} ∈ E`). -/
def walks2 : Finset (Fin n × Fin n × Fin n) :=
  univ.filter fun w => G.Adj w.1 w.2.1 ∧ G.Adj w.2.1 w.2.2

/-- `P(x, ∗, ∗)`: the 2-walks starting at `x`. -/
def walksFrom (x : Fin n) : Finset (Fin n × Fin n × Fin n) := (walks2 G).filter fun w => w.1 = x

theorem hasFourCycle_iff :
    HasFourCycle G ↔ ∃ x z, x ≠ z ∧ 2 ≤ #(commonNbrs G x z) := by
  constructor
  · rintro ⟨v, c, hc, hl⟩
    rcases c with _ | ⟨h1, c⟩; · simp at hl
    rcases c with _ | ⟨h2, c⟩; · simp at hl
    rcases c with _ | ⟨h3, c⟩; · simp at hl
    rcases c with _ | ⟨h4, c⟩; · simp at hl
    rcases c with _ | ⟨h5, c⟩
    · rw [Walk.cons_isCycle_iff] at hc
      obtain ⟨hp, -⟩ := hc
      simp only [Walk.cons_isPath_iff, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false, Walk.isPath_iff_nil] at hp
      rename_i a b c'
      refine ⟨v, b, ?_, ?_⟩
      · rintro rfl; tauto
      · rw [Nat.succ_le_iff, one_lt_card]
        exact ⟨a, by simp [commonNbrs, h1, h2], c', by simp [commonNbrs, h3.symm, h4.symm],
          fun h => by subst h; tauto⟩
    · simp at hl
  · rintro ⟨x, z, hxz, h2⟩
    rw [Nat.succ_le_iff, one_lt_card] at h2
    obtain ⟨y, hy, y', hy', hne⟩ := h2
    simp only [commonNbrs, mem_filter, mem_univ, true_and] at hy hy'
    refine ⟨x, .cons hy.1 (.cons hy.2 (.cons hy'.2.symm (.cons hy'.1.symm .nil))), ?_, rfl⟩
    have := hy.1.ne; have := hy.2.ne; have := hy'.1.ne; have := hy'.2.ne
    rw [Walk.cons_isCycle_iff]
    simp only [Walk.cons_isPath_iff, Walk.support_cons, Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false, Walk.isPath_iff_nil, Walk.edges_cons, Walk.edges_nil,
      Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk]
    refine ⟨⟨⟨⟨Walk.Nil.nil, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> grind

/-! ### Phase 1 -/

theorem card_walksFrom_eq_sum_commonNbrs (x : Fin n) :
    #(walksFrom G x) = ∑ z, #(commonNbrs G x z) := by
  rw [← card_sigma]
  refine card_bij (fun w _ => ⟨w.2.2, w.2.1⟩) ?_ ?_ ?_
  · intro w hw
    simp only [walksFrom, walks2, mem_filter, mem_univ, true_and] at hw
    obtain ⟨⟨h1, h2⟩, rfl⟩ := hw
    simp [commonNbrs, h1, h2]
  · rintro ⟨a, b, c⟩ hw ⟨a', b', c'⟩ hw' h
    simp only [walksFrom, walks2, mem_filter, mem_univ, true_and] at hw hw'
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simp only [heq_eq_eq] at h2
    subst h2
    simp only [Prod.mk.injEq, and_true]
    exact hw.2.trans hw'.2.symm
  · intro p hp
    simp only [mem_sigma, mem_univ, true_and, commonNbrs, mem_filter] at hp
    exact ⟨(x, p.2, p.1), by simp [walksFrom, walks2, hp], rfl⟩

theorem card_walksFrom_eq_sum_degree (x : Fin n) :
    #(walksFrom G x) = ∑ y ∈ G.neighborFinset x, G.degree y := by
  simp_rw [← card_neighborFinset_eq_degree]
  rw [← card_sigma]
  refine card_bij (fun w _ => ⟨w.2.1, w.2.2⟩) ?_ ?_ ?_
  · intro w hw
    simp only [walksFrom, walks2, mem_filter, mem_univ, true_and] at hw
    obtain ⟨⟨h1, h2⟩, rfl⟩ := hw
    simp [h1, h2]
  · rintro ⟨a, b, c⟩ hw ⟨a', b', c'⟩ hw' h
    simp only [walksFrom, walks2, mem_filter, mem_univ, true_and] at hw hw'
    simp only [Sigma.mk.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    simp only [heq_eq_eq] at h2
    subst h2
    simp only [Prod.mk.injEq, and_true]
    exact hw.2.trans hw'.2.symm
  · intro p hp
    simp only [mem_sigma, mem_neighborFinset] at hp
    exact ⟨(x, p.1, p.2), by simp [walksFrom, walks2, hp], rfl⟩

/-- Phase 1 of the 4-cycle algorithm: if `|P(x,∗,∗)| ≥ 2n − 1` then `|P(x,∗,z)| ≥ 2` for some
`z ≠ x`, hence there is a 4-cycle. -/
theorem exists_of_card_walksFrom {x : Fin n} (h : 2 * n - 1 ≤ #(walksFrom G x)) :
    ∃ z, x ≠ z ∧ 2 ≤ #(commonNbrs G x z) := by
  by_contra hc
  push Not at hc
  rw [card_walksFrom_eq_sum_commonNbrs, ← add_sum_erase _ _ (mem_univ x)] at h
  have h1 : #(commonNbrs G x x) ≤ n - 1 := by
    have : commonNbrs G x x ⊆ univ.erase x := by
      intro y hy; simp only [commonNbrs, mem_filter] at hy
      simpa using hy.2.1.ne'
    simpa using card_le_card this
  have h2 : ∑ z ∈ univ.erase x, #(commonNbrs G x z) ≤ ∑ z ∈ univ.erase x, 1 :=
    sum_le_sum fun z hz => by have := hc z (ne_of_mem_erase hz).symm; omega
  simp at h2
  have := x.pos
  omega

theorem sum_card_walksFrom : ∑ x, #(walksFrom G x) = #(walks2 G) := by
  rw [← card_biUnion]
  · congr 1; ext w; simp [walksFrom]
  · intro x _ x' _ h
    simp only [Function.onFun]
    rw [Finset.disjoint_left]; intro w hw hw'
    simp only [walksFrom, mem_filter] at hw hw'
    exact h (hw.2.symm.trans hw'.2)

theorem sum_degree_sq : ∑ y, G.degree y ^ 2 = #(walks2 G) := by
  rw [show walks2 G = univ.biUnion (fun y => (walks2 G).filter fun w => w.2.1 = y) by
    ext w; simp, card_biUnion]
  · have : ∀ y, #((walks2 G).filter fun w => w.2.1 = y) = G.degree y ^ 2 := by
      intro y
      rw [sq, ← card_neighborFinset_eq_degree, ← card_product]
      refine card_bij (fun w _ => (w.1, w.2.2)) ?_ ?_ ?_
      · intro w hw
        simp only [walks2, mem_filter, mem_univ, true_and] at hw
        obtain ⟨⟨h1, h2⟩, rfl⟩ := hw
        simp [mem_neighborFinset, h1.symm, h2]
      · intro w hw w' hw' h
        simp only [walks2, mem_filter, mem_univ, true_and] at hw hw'
        simp only [Prod.mk.injEq] at h
        ext <;> simp_all
      · intro p hp
        simp only [mem_product, mem_neighborFinset] at hp
        exact ⟨(p.1, y, p.2), by simp [walks2, hp, G.adj_comm _ y], rfl⟩
    simp_rw [this]
  · intro x _ x' _ h
    simp only [Function.onFun]
    rw [Finset.disjoint_left]; intro w hw hw'
    simp only [mem_filter] at hw hw'
    exact h (hw.2.symm.trans hw'.2)

/-- If Phase 1 does not stop, then `∑_y deg(y)² < 2n²`. -/
theorem sum_degree_sq_lt (hpos : 0 < n) (h : ∀ x, #(walksFrom G x) < 2 * n - 1) :
    ∑ y, G.degree y ^ 2 < 2 * n ^ 2 := by
  rw [sum_degree_sq, ← sum_card_walksFrom]
  calc ∑ x, #(walksFrom G x) ≤ ∑ _x : Fin n, (2 * n - 2) :=
        sum_le_sum fun x _ => by have := h x; omega
    _ = n * (2 * n - 2) := by simp
    _ < 2 * n ^ 2 := by
        rcases n with _ | n
        · omega
        · simp only [sq]
          rw [show 2 * (n + 1) - 2 = 2 * n by omega]; nlinarith

/-! ### Partitioning a neighbourhood into chunks of size at most 8 -/

/-- Rank of `x` in `s`: the number of smaller elements. -/
def rank (s : Finset (Fin n)) (x : Fin n) : ℕ := #(s.filter (· < x))

lemma rank_lt_rank {s : Finset (Fin n)} {x x' : Fin n} (hx : x ∈ s) (h : x < x') :
    rank s x < rank s x' := by
  refine card_lt_card ⟨fun y hy => ?_, fun hsub => ?_⟩
  · simp only [mem_filter] at hy ⊢; exact ⟨hy.1, hy.2.trans h⟩
  · have := hsub (mem_filter.2 ⟨hx, h⟩); simp at this

lemma rank_injOn (s : Finset (Fin n)) : Set.InjOn (rank s) s := by
  intro x hx x' hx' h
  rcases lt_trichotomy x x' with hlt | heq | hgt
  · exact absurd h (rank_lt_rank hx hlt).ne
  · exact heq
  · exact absurd h (rank_lt_rank hx' hgt).ne'

lemma rank_lt_card {s : Finset (Fin n)} {x : Fin n} (hx : x ∈ s) : rank s x < #s :=
  card_lt_card ⟨filter_subset _ _, fun h => by have := h hx; simp at this⟩

lemma exists_rank_eq (s : Finset (Fin n)) {c : ℕ} (hc : c < #s) : ∃ t ∈ s, rank s t = c := by
  have himg : s.image (rank s) = range #s := by
    refine eq_of_subset_of_card_le (fun r hr => ?_) ?_
    · obtain ⟨x, hx, rfl⟩ := mem_image.1 hr; exact mem_range.2 (rank_lt_card hx)
    · rw [card_image_of_injOn (rank_injOn s)]; simp
  have : c ∈ s.image (rank s) := by rw [himg]; exact mem_range.2 hc
  simpa using this

/-- `chunk s T t`: the part of `s` assigned to `t ∈ T` (`N_A(y,a)` with `s = N(y)`, `T = A(y)`):
the elements of `s` whose rank divided by 8 is the rank of `t` in `T`. -/
def chunk (s T : Finset (Fin n)) (t : Fin n) : Finset (Fin n) :=
  if t ∈ T then s.filter (fun x => rank s x / 8 = rank T t) else ∅

lemma chunk_subset (s T : Finset (Fin n)) (t : Fin n) : chunk s T t ⊆ s := by
  unfold chunk; split_ifs <;> simp

lemma card_chunk_le (s T : Finset (Fin n)) (t : Fin n) : #(chunk s T t) ≤ 8 := by
  unfold chunk; split_ifs
  · calc #(s.filter (fun x => rank s x / 8 = rank T t))
          = #((s.filter (fun x => rank s x / 8 = rank T t)).image (rank s)) :=
            (card_image_of_injOn ((rank_injOn s).mono (by intro x hx; simp at hx; exact hx.1))).symm
        _ ≤ #(Ico (8 * rank T t) (8 * rank T t + 8)) := by
            refine card_le_card fun r hr => ?_
            obtain ⟨x, hx, rfl⟩ := mem_image.1 hr
            simp only [mem_filter] at hx
            simp only [mem_Ico]; omega
        _ = 8 := by simp
  · simp

lemma exists_mem_chunk {s T : Finset (Fin n)} (h : #s ≤ 8 * #T) {x : Fin n} (hx : x ∈ s) :
    ∃ t ∈ T, x ∈ chunk s T t := by
  have := rank_lt_card hx
  obtain ⟨t, ht, hr⟩ := exists_rank_eq T (c := rank s x / 8) (by omega)
  exact ⟨t, ht, by simp [chunk, ht, hx, hr]⟩

lemma eq_of_mem_chunk {s T : Finset (Fin n)} {x t t' : Fin n} (h : x ∈ chunk s T t)
    (h' : x ∈ chunk s T t') : t = t' := by
  unfold chunk at h h'
  split_ifs at h h' with ht ht'
  · simp only [mem_filter] at h h'
    exact rank_injOn T ht ht' (h.2.symm.trans h'.2)
  all_goals simp at h h'

/-! ### Lemma 13 -/

/-- The degree vector. -/
def degs : Fin n → ℕ := fun y => G.degree y

/-- `W(b)`: the 2-walks `(x, y, z)` with `z ∈ N_B(y, b)`, i.e. the union of the sets
`W(y, b) = N(y) × {y} × N_B(y, b)` over the `y` with `b ∈ B(y)`. -/
def Wset (b : Fin n) : Finset (Fin n × Fin n × Fin n) :=
  (walks2 G).filter fun w =>
    w.2.2 ∈ chunk (G.neighborFinset w.2.1) (tileB n (degs G) w.2.1) b

/-- The paper's hypothesis of the second phase: `∑_y deg(y)² < 2n²`. -/
def Phase2 : Prop := ∑ y, G.degree y ^ 2 < 2 * n ^ 2

lemma degs_lt (y : Fin n) : degs G y < n := by
  simpa [degs] using G.degree_lt_card_verts y

lemma degree_le_eight_mul_tileA (hG : Phase2 G) (y : Fin n) :
    G.degree y ≤ 8 * #(tileA n (degs G) y) := by
  rw [card_tileA (degs_lt G) hG]; exact le_eight_mul_tileSize _

lemma degree_le_eight_mul_tileB (hG : Phase2 G) (y : Fin n) :
    G.degree y ≤ 8 * #(tileB n (degs G) y) := by
  rw [card_tileB (degs_lt G) hG]; exact le_eight_mul_tileSize _

/-- Lemma 13 of [Censor-Hillel et al., PODC 2015]: the sets `W(b)` form a partition of
`P(∗,∗,∗)`, and `|W(b)| ≤ 64 n` for each `b` (under the hypothesis of the second phase). -/
theorem lemma_13 (hG : Phase2 G) :
    (∀ w ∈ walks2 G, ∃! b, w ∈ Wset G b) ∧ (∀ b, Wset G b ⊆ walks2 G) ∧
      ∀ b, #(Wset G b) ≤ 64 * n := by
  refine ⟨fun w hw => ?_, fun b => filter_subset _ _, fun b => ?_⟩
  · have hz : w.2.2 ∈ G.neighborFinset w.2.1 := by
      simp only [walks2, mem_filter] at hw; simpa using hw.2.2
    obtain ⟨b, -, hb⟩ := exists_mem_chunk (T := tileB n (degs G) w.2.1) (by
      rw [card_neighborFinset_eq_degree]; exact degree_le_eight_mul_tileB G hG _) hz
    refine ⟨b, mem_filter.2 ⟨hw, hb⟩, fun b' hb' => ?_⟩
    exact (eq_of_mem_chunk hb (mem_filter.1 hb').2).symm
  · set A := tileA n (degs G)
    set B := tileB n (degs G)
    set Y := univ.filter fun y => b ∈ B y
    have hsub : Wset G b ⊆ Y.biUnion fun y =>
        G.neighborFinset y ×ˢ ({y} ×ˢ chunk (G.neighborFinset y) (B y) b) := by
      intro w hw
      simp only [Wset, walks2, mem_filter, mem_univ, true_and] at hw
      have hb : b ∈ B w.2.1 := by
        by_contra hb
        simp only [chunk] at hw
        split_ifs at hw with h
        · exact hb h
        · simp at hw
      simp only [mem_biUnion, mem_filter, mem_univ, true_and, mem_product, mem_singleton,
        mem_neighborFinset, Y]
      exact ⟨w.2.1, hb, hw.1.1.symm, rfl, hw.2⟩
    -- the sets `A(y)`, `y ∈ Y`, are pairwise disjoint
    have hdisj : (Y : Set (Fin n)).PairwiseDisjoint A := by
      intro y hy y' hy' hne
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, Y] at hy hy'
      rw [Function.onFun, Finset.disjoint_left]
      intro a ha ha'
      have : Disjoint (A y ×ˢ B y) (A y' ×ˢ B y') := tiles_disjoint (degs_lt G) hG hne
      rw [Finset.disjoint_left] at this
      exact this (a := (a, b)) (mem_product.2 ⟨ha, hy⟩) (mem_product.2 ⟨ha', hy'⟩)
    calc #(Wset G b) ≤ ∑ y ∈ Y, #(G.neighborFinset y ×ˢ ({y} ×ˢ
            chunk (G.neighborFinset y) (B y) b)) :=
          (card_le_card hsub).trans card_biUnion_le
      _ ≤ ∑ y ∈ Y, 8 * (8 * #(A y)) := by
          refine sum_le_sum fun y _ => ?_
          rw [card_product, card_product, card_singleton, one_mul, card_neighborFinset_eq_degree]
          have := card_chunk_le (G.neighborFinset y) (B y) b
          have : G.degree y ≤ 8 * #(A y) := degree_le_eight_mul_tileA G hG y
          calc G.degree y * #(chunk (G.neighborFinset y) (B y) b) ≤ G.degree y * 8 :=
                Nat.mul_le_mul_left _ ‹_›
            _ ≤ 8 * (8 * #(A y)) := by omega
      _ = 64 * #(Y.biUnion A) := by
          rw [card_biUnion hdisj, mul_sum]; congr 1; ext y; ring
      _ ≤ 64 * n := Nat.mul_le_mul_left _ (by simpa using card_le_univ (Y.biUnion A))

end Podc.AlgebraicCongestedClique
