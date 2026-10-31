import Papers.PODC2021.WakeUpMatching.Basic

/-!
# Theorem 6.3: minimum NAF load = matching cover number (unless it is 1)

Dani, Gupta, Hayes, Pettie, PODC 2021 (arXiv:2104.09096v2), Theorem 6.3.

*Easy direction* (`exists_naf_of_cover`): `k` matchings covering `V` give a NAF of load `≤ k`
(send `v` to its partner in some matching containing it).

*Hard direction* (`exists_cover_of_naf`): for `L ≥ 2`, a NAF of load `≤ L` gives `L` matchings
covering `V`. The paper's proof repeatedly redirects `f (f v)` to a load-zero vertex `v`; as
written that process need not terminate (applied to a leaf of a star with a bidirected edge it
cycles) and the claimed final shape (cycles and stars) is not exactly what one gets. We use an
extremal version of the same local move instead:

* `bad f = {v | f (f (f v)) ≠ f v}` (the image of `v` is not on a 2-cycle);
* the move `f (f v) := v` for `v ∈ bad f` with load `< L` keeps a NAF of load `≤ L` and strictly
  shrinks `bad f` (`card_bad_move_lt`);
* if every bad vertex has load `L ≥ 2`, then all its in-neighbours are bad, so counting in-edges
  inside `bad f` gives `2 |bad f| ≤ |bad f|`, i.e. `bad f = ∅` (`bad_eq_empty`).

So there is a NAF `g` of load `≤ L` with `g ∘ g ∘ g = g` (every component is a "double star"
around a 2-cycle). For such `g`, label the in-neighbours of each vertex injectively by `Fin L`
and put the edge `{x, g x}` into matching number `label x` whenever every in-neighbour of `x`
is `g x`; this gives `L` matchings covering `V` (`exists_cover_of_tidy`).
-/

set_option linter.unusedSectionVars false

namespace Podc.WakeUpMatching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-! ### Easy direction -/

/-- Theorem 6.3, first part of the proof: `k` matchings covering `V` give a NAF of load `≤ k`.
-- CSLib candidate -/
theorem exists_naf_of_cover {k : ℕ} {M : Fin k → G.Subgraph} (hM : IsMatchingCover G M) :
    ∃ f, IsNAF G f ∧ ∀ w, inDeg f w ≤ k := by
  choose i hi using hM.2
  choose f hf using fun v => (hM.1 (i v) (hi v)).exists
  refine ⟨f, fun v => (M (i v)).adj_sub (hf v), fun w => ?_⟩
  calc inDeg f w ≤ #(univ : Finset (Fin k)) := by
        refine card_le_card_of_injOn i (fun _ _ => mem_coe.2 (mem_univ _)) ?_
        intro x hx y hy hxy
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
        have hx' : (M (i x)).Adj w x := hx ▸ (hf x).symm
        have hy' : (M (i x)).Adj w y := hxy ▸ hy ▸ (hf y).symm
        exact (hM.1 (i x) ((M (i x)).edge_vert hx')).unique hx' hy'
    _ = k := by simp

/-! ### The extremal normalisation -/

/-- Vertices whose image is not on a 2-cycle of `f`. -/
def bad (f : V → V) : Finset V := {v | f (f (f v)) ≠ f v}

/-- The paper's local move: redirect `f (f v)` to `v`. -/
def move (f : V → V) (v : V) : V → V := Function.update f (f v) v

theorem move_isNAF {f : V → V} (hf : IsNAF G f) (v : V) : IsNAF G (move f v) := by
  intro x
  unfold move
  by_cases hx : x = f v
  · subst hx; simpa using (hf v).symm
  · rw [Function.update_of_ne hx]; exact hf x

theorem inDeg_move_le {f : V → V} {L : ℕ} (hl : ∀ w, inDeg f w ≤ L) {v : V}
    (hv : inDeg f v < L) (w : V) : inDeg (move f v) w ≤ L := by
  unfold inDeg move
  by_cases hw : w = v
  · subst hw
    calc #{x | Function.update f (f w) w x = w} ≤ #(insert (f w) ({x | f x = w} : Finset V)) := by
          apply card_le_card
          intro x hx
          simp only [mem_filter, mem_univ, true_and] at hx
          by_cases hx' : x = f w
          · simp [hx']
          · rw [Function.update_of_ne hx'] at hx; simp [hx]
      _ ≤ #{x | f x = w} + 1 := card_insert_le _ _
      _ ≤ L := hv
  · calc #{x | Function.update f (f v) v x = w} ≤ #{x | f x = w} := by
          apply card_le_card
          intro x hx
          simp only [mem_filter, mem_univ, true_and] at hx ⊢
          by_cases hx' : x = f v
          · subst hx'; simp at hx; exact absurd hx.symm hw
          · rwa [Function.update_of_ne hx'] at hx
      _ ≤ L := hl w

theorem bad_move_subset {f : V → V} (hf : IsNAF G f) {v : V} (hv : v ∈ bad f) :
    bad (move f v) ⊆ (bad f).erase v := by
  have hvu : v ≠ f v := (hf v).ne
  have hbad : f (f (f v)) ≠ f v := by simpa [bad] using hv
  set u := f v with hu
  have e1 : move f v u = v := by simp [move, ← hu]
  have e2 : ∀ y, y ≠ u → move f v y = f y := fun y hy => by
    simp only [move, ← hu]; exact Function.update_of_ne hy _ _
  intro x hx
  simp only [bad, mem_filter, mem_univ, true_and, mem_erase] at hx ⊢
  refine ⟨?_, ?_⟩
  · rintro rfl
    apply hx
    rw [e2 x hvu, ← hu, e1, e2 x hvu]
  · intro hx'
    apply hx
    by_cases h1 : x = u
    · subst h1; rw [e1, e2 v hvu, e1]
    · rw [e2 x h1]
      by_cases h2 : f x = u
      · rw [h2, e1, e2 v hvu]
      · rw [e2 _ h2]
        by_cases h3 : f (f x) = u
        · exfalso
          have hfu : f u = f x := by rw [← h3]; exact hx'
          apply hbad
          rw [hfu, h3]
        · rw [e2 _ h3, hx']

theorem card_bad_move_lt {f : V → V} (hf : IsNAF G f) {v : V} (hv : v ∈ bad f) :
    #(bad (move f v)) < #(bad f) :=
  (card_le_card (bad_move_subset hf hv)).trans_lt (card_erase_lt_of_mem hv)

/-- All in-neighbours of a bad vertex are bad. -/
theorem mem_bad_of_map_mem_bad {f : V → V} {x : V} (hx : f x ∈ bad f) : x ∈ bad f := by
  simp only [bad, mem_filter, mem_univ, true_and] at hx ⊢
  intro h; apply hx; rw [h]

/-- If every bad vertex has load `≥ L ≥ 2`, there is no bad vertex. -/
theorem bad_eq_empty {f : V → V} {L : ℕ} (hL : 2 ≤ L) (h : ∀ v ∈ bad f, L ≤ inDeg f v) :
    bad f = ∅ := by
  have hsum : #({x | f x ∈ bad f} : Finset V) = ∑ b ∈ bad f, inDeg f b := by
    rw [card_eq_sum_card_fiberwise (f := f) (t := bad f) (fun x hx => by simpa using hx)]
    refine sum_congr rfl fun b _ => ?_
    unfold inDeg; congr 1; ext x; simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · rintro rfl; exact ⟨by assumption, rfl⟩
  have hle : #({x | f x ∈ bad f} : Finset V) ≤ #(bad f) :=
    card_le_card fun x hx => mem_bad_of_map_mem_bad (by simpa using hx)
  have hge : L * #(bad f) ≤ ∑ b ∈ bad f, inDeg f b := by
    rw [mul_comm, ← smul_eq_mul, ← sum_const]; exact sum_le_sum h
  have h2 : 2 * #(bad f) ≤ L * #(bad f) := Nat.mul_le_mul_right _ hL
  have : #(bad f) = 0 := by omega
  exact card_eq_zero.1 this

/-- Normalisation: for `L ≥ 2`, a NAF of load `≤ L` can be turned into one of load `≤ L` with
`g ∘ g ∘ g = g`. -/
theorem exists_tidy {L : ℕ} (hL : 2 ≤ L) :
    ∀ (n : ℕ) (f : V → V), #(bad f) = n → IsNAF G f → (∀ w, inDeg f w ≤ L) →
      ∃ g, IsNAF G g ∧ (∀ w, inDeg g w ≤ L) ∧ ∀ v, g (g (g v)) = g v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hn hf hl
    by_cases h : ∃ v ∈ bad f, inDeg f v < L
    · obtain ⟨v, hv, hlt⟩ := h
      exact ih _ (hn ▸ card_bad_move_lt hf hv) (move f v) rfl (move_isNAF hf v)
        (inDeg_move_le hl hlt)
    · push Not at h
      have h0 := bad_eq_empty hL h
      refine ⟨f, hf, hl, fun v => ?_⟩
      by_contra hv
      have : v ∈ bad f := by simp [bad, hv]
      simp [h0] at this

/-! ### Matchings from a normalised NAF -/

theorem exists_injOn_fin {s : Finset V} {L : ℕ} (hL : 1 ≤ L) (hs : #s ≤ L) :
    ∃ e : V → Fin L, Set.InjOn e s := by
  refine ⟨fun x => if h : x ∈ s then Fin.castLE hs (s.equivFin ⟨x, h⟩) else ⟨0, hL⟩, ?_⟩
  intro x hx y hy hxy
  simp only [mem_coe] at hx hy
  simp only [hx, hy, dite_true] at hxy
  have := s.equivFin.injective (Fin.castLE_injective hs hxy)
  simpa using this

/-- The `L` matchings built from a normalised NAF `g` and a fibre-injective labelling `c`. -/
def tidyAdj (g : V → V) (c : V → Fin L) (i : Fin L) (a b : V) : Prop :=
  ((∀ y, g y = a → y = g a) ∧ c a = i ∧ g a = b) ∨
    ((∀ y, g y = b → y = g b) ∧ c b = i ∧ g b = a)

/-- The subgraph with adjacency `tidyAdj`. -/
def tidySubgraph (hg : IsNAF G g) (c : V → Fin L) (i : Fin L) : G.Subgraph where
  verts := {v | ∃ w, tidyAdj g c i v w}
  Adj := tidyAdj g c i
  adj_sub := by
    rintro a b (⟨-, -, rfl⟩ | ⟨-, -, rfl⟩)
    · exact hg a
    · exact (hg b).symm
  edge_vert h := ⟨_, h⟩
  symm := ⟨fun _ _ h => h.symm⟩

theorem tidyAdj_unique {g : V → V} {c : V → Fin L}
    (hc : ∀ x y, g x = g y → c x = c y → x = y) {i : Fin L} {v w₁ w₂ : V}
    (h₁ : tidyAdj g c i v w₁) (h₂ : tidyAdj g c i v w₂) : w₁ = w₂ := by
  rcases h₁ with ⟨a1, -, g1⟩ | ⟨a1, c1, g1⟩ <;> rcases h₂ with ⟨a2, -, e2⟩ | ⟨a2, c2, g2⟩
  · exact g1.symm.trans e2
  · rw [a1 _ g2, g1]
  · rw [a2 _ g1, e2]
  · exact hc _ _ (g1.trans g2.symm) (c1.trans c2.symm)

/-- Theorem 6.3, hard direction for a normalised NAF: `L` matchings cover `V`. -/
theorem exists_cover_of_tidy {L : ℕ} (hL : 1 ≤ L) {g : V → V} (hg : IsNAF G g)
    (hl : ∀ w, inDeg g w ≤ L) (h3 : ∀ v, g (g (g v)) = g v) :
    ∃ M : Fin L → G.Subgraph, IsMatchingCover G M := by
  choose e he using fun p => exists_injOn_fin (s := {x | g x = p}) hL (hl p)
  set c : V → Fin L := fun x => e (g x) x
  have hc : ∀ x y, g x = g y → c x = c y → x = y := by
    intro x y hxy h
    simp only [c] at h
    rw [hxy] at h
    exact he (g y) (by simpa using hxy) (by simp) h
  refine ⟨tidySubgraph hg c, fun i v hv => ?_, fun v => ?_⟩
  · obtain ⟨w, hw⟩ := hv
    exact ⟨w, hw, fun y hy => tidyAdj_unique hc hy hw⟩
  · by_cases hact : ∀ y, g y = v → y = g v
    · exact ⟨c v, g v, Or.inl ⟨hact, rfl, rfl⟩⟩
    · push Not at hact
      obtain ⟨y, hyv, hne⟩ := hact
      have hacty : ∀ z, g z = y → z = g y := by
        intro z hz
        exfalso; apply hne
        have := h3 z
        rw [hz, hyv] at this
        exact this.symm
      exact ⟨c y, y, Or.inr ⟨hacty, rfl, hyv⟩⟩

/-- Theorem 6.3, hard direction: for `L ≥ 2`, a NAF of load `≤ L` yields `L` matchings covering
all vertices. -- CSLib candidate -/
theorem exists_cover_of_naf {L : ℕ} (hL : 2 ≤ L) {f : V → V} (hf : IsNAF G f)
    (hl : ∀ w, inDeg f w ≤ L) : ∃ M : Fin L → G.Subgraph, IsMatchingCover G M := by
  obtain ⟨g, hg, hgl, h3⟩ := exists_tidy hL _ f rfl hf hl
  exact exists_cover_of_tidy (by omega) hg hgl h3

/-- Theorem 6.3 in threshold form: for `k ≥ 2`, `G` has a NAF of load `≤ k` iff `k` matchings
cover `V`. -/
theorem exists_naf_iff_exists_cover {k : ℕ} (hk : 2 ≤ k) :
    (∃ f, IsNAF G f ∧ load f ≤ k) ↔ ∃ M : Fin k → G.Subgraph, IsMatchingCover G M := by
  constructor
  · rintro ⟨f, hf, hl⟩; exact exists_cover_of_naf hk hf (load_le_iff.1 hl)
  · rintro ⟨M, hM⟩
    obtain ⟨f, hf, hl⟩ := exists_naf_of_cover hM
    exact ⟨f, hf, load_le_iff.2 hl⟩

/-! ### Theorem 6.3 -/

/-- A NAF exists iff `G` has no isolated vertex. -/
theorem exists_naf_iff : (∃ f, IsNAF G f) ↔ ∀ v, ∃ w, G.Adj v w :=
  ⟨fun ⟨f, hf⟩ v => ⟨f v, hf v⟩, fun h => ⟨fun v => (h v).choose, fun v => (h v).choose_spec⟩⟩

theorem minNAFLoad_spec (hG : ∀ v, ∃ w, G.Adj v w) :
    ∃ f, IsNAF G f ∧ load f = minNAFLoad G := by
  obtain ⟨f, hf⟩ := exists_naf_iff.2 hG
  exact Nat.sInf_mem (s := {L | ∃ f, IsNAF G f ∧ load f = L}) ⟨_, f, hf, rfl⟩

theorem minNAFLoad_le {f : V → V} (hf : IsNAF G f) : minNAFLoad G ≤ load f :=
  Nat.sInf_le ⟨f, hf, rfl⟩

theorem matchingCoverNumber_le {k : ℕ} {M : Fin k → G.Subgraph} (hM : IsMatchingCover G M) :
    matchingCoverNumber G ≤ k :=
  Nat.sInf_le ⟨M, hM⟩

/-- First half of the proof of Theorem 6.3: the minimum NAF load is at most `mc(G)`. -/
theorem minNAFLoad_le_matchingCoverNumber (hG : ∀ v, ∃ w, G.Adj v w) :
    minNAFLoad G ≤ matchingCoverNumber G := by
  obtain ⟨f, hf, hfl⟩ := minNAFLoad_spec hG
  -- a matching cover exists (here: from the NAF, with `max 2 (load f)` matchings)
  have hne : {k | ∃ M : Fin k → G.Subgraph, IsMatchingCover G M}.Nonempty :=
    ⟨_, exists_cover_of_naf (le_max_left 2 (load f)) hf
      (fun w => (inDeg_le_load f w).trans (le_max_right _ _))⟩
  obtain ⟨M, hM⟩ := Nat.sInf_mem hne
  obtain ⟨f', hf', hl'⟩ := exists_naf_of_cover hM
  exact (minNAFLoad_le hf').trans (load_le_iff.2 hl')

/-- **Theorem 6.3** of the paper: for every graph `G` (without isolated vertices, so that NAFs
and matching covers exist), the minimum NAF load of `G` equals its matching cover number,
unless the minimum NAF load is `1`. -/
theorem theorem_6_3 (hG : ∀ v, ∃ w, G.Adj v w) (h1 : minNAFLoad G ≠ 1) :
    minNAFLoad G = matchingCoverNumber G := by
  refine le_antisymm (minNAFLoad_le_matchingCoverNumber hG) ?_
  obtain ⟨f, hf, hfl⟩ := minNAFLoad_spec hG
  rcases Nat.lt_or_ge (minNAFLoad G) 2 with h | h
  · have h0 : minNAFLoad G = 0 := by omega
    have hV : IsEmpty V := ⟨fun v => by
      have h1 : 1 ≤ inDeg f (f v) := card_pos.2 ⟨v, by simp⟩
      have := inDeg_le_load f (f v)
      omega⟩
    have : matchingCoverNumber G ≤ 0 :=
      matchingCoverNumber_le (M := Fin.elim0) ⟨fun i => i.elim0, fun v => hV.elim v⟩
    omega
  · obtain ⟨M, hM⟩ := exists_cover_of_naf h hf (fun w => hfl ▸ inDeg_le_load f w)
    exact matchingCoverNumber_le hM

/-- **Theorem 6.3**, second sentence: if the minimum NAF load is `1`, the matching cover number
is `1` or `2`. -/
theorem theorem_6_3_load_one (hG : ∀ v, ∃ w, G.Adj v w) (h1 : minNAFLoad G = 1) :
    matchingCoverNumber G = 1 ∨ matchingCoverNumber G = 2 := by
  have hlo := minNAFLoad_le_matchingCoverNumber hG
  obtain ⟨f, hf, hfl⟩ := minNAFLoad_spec hG
  obtain ⟨M, hM⟩ := exists_cover_of_naf (le_refl 2) hf
    (fun w => (inDeg_le_load f w).trans (by omega))
  have := matchingCoverNumber_le hM
  omega

end Podc.WakeUpMatching
