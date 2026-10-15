import Papers.PODC2026.RankingOpinions.Layers

/-!
# Two facts about the stable braket multiset `⋃_p f(G_p)`

Used in the proof of Lemma 6.12 (and Lemma 6.5) of Breitkopf–Dallot–El-Hayek–Schmid, PODC 2026:
which bras a given ket can be attached to once Circles has stabilized.
-/

namespace RankingOpinions

open Finset

variable {k : ℕ}

/-- If `g` lies strictly (clockwise, without wrapping) before the ket `e.2` of a braket `e` of the
circle of `G`, and `g ∈ G`, then the bra `e.1` lies in `[g, e.2)`. -/
lemma bra_bound_circle {G : Finset (Fin k)} {e : Braket k} (he : e ∈ circle G) {g : Fin k}
    (hg : g ∈ G) (hlt : g.val < e.2.val) : g.val ≤ e.1.val ∧ e.1.val < e.2.val := by
  rw [mem_circle] at he
  obtain ⟨h1, h2⟩ := he
  have hmin := nxt_min h1 hg
  rw [← h2] at hmin
  have hne : e.2 ≠ e.1 := by
    intro e'
    have := (nxt_eq_self_iff h1).1 (h2 ▸ e')
    rw [this, mem_singleton] at hg
    rw [hg] at hlt; rw [e'] at hlt; omega
  have hv : e.2.val ≠ e.1.val := fun h => hne (Fin.ext h)
  have := e.1.isLt; have := e.2.isLt; have := g.isLt
  rw [w_val, w_val] at hmin
  split_ifs at hmin <;> omega

/-- In `⋃_p f(G_p)`: if a color `g` with more supporters than the ket `e.2` lies before `e.2`, then
the bra `e.1` lies in `[g, e.2)`. -/
lemma bra_bound_layers {y : Fin k → ℕ} {e : Braket k} (he : e ∈ layers y) {g : Fin k}
    (hlt : g.val < e.2.val) (hy : y e.2 < y g) : g.val ≤ e.1.val ∧ e.1.val < e.2.val := by
  rw [mem_layers] at he
  obtain ⟨p, -, hp⟩ := he
  have h2 : e.2 ∈ greedy y (p + 1) := by
    rw [mem_circle] at hp; rw [hp.2]; exact nxt_mem hp.1
  have hg : g ∈ greedy y (p + 1) := by
    simp only [greedy, mem_filter, mem_univ, true_and] at h2 ⊢; omega
  exact bra_bound_circle hp hg hlt

/-- In `⋃_p f(G_p)`: the braket `⟨g|h⟩` occurs if `g < h`, `h` has at least one supporter but
fewer than `g`, and every color strictly between `g` and `h` has fewer supporters than `h`. -/
lemma mem_layers_of_gap {y : Fin k → ℕ} {g h : Fin k} (hlt : g.val < h.val) (hpos : 1 ≤ y h)
    (hy : y h < y g) (hgap : ∀ c : Fin k, g.val < c.val → c.val < h.val → y c < y h) :
    (g, h) ∈ layers y := by
  rw [mem_layers]
  refine ⟨y h - 1, ?_, ?_⟩
  · have := Finset.le_sup (f := y) (mem_univ h); omega
  · rw [Nat.sub_add_cancel hpos, mem_circle]
    set G := greedy y (y h)
    have hgG : g ∈ G := by simp [G, greedy]; omega
    have hhG : h ∈ G := by simp [G, greedy]
    refine ⟨hgG, ?_⟩
    simp only
    by_contra hne
    have hlt' := nxt_lt hgG hhG hne
    have hmem := nxt_mem hgG
    set c := nxt G g
    have hc : y h ≤ y c := by simpa [G, greedy] using hmem
    have := g.isLt; have := h.isLt; have := c.isLt
    have hgh : g.val ≠ h.val := by omega
    rw [w_val, w_val] at hlt'
    by_cases h1 : g.val < c.val
    · by_cases h2 : c.val < h.val
      · have := hgap c h1 h2; omega
      · split_ifs at hlt' <;> omega
    · split_ifs at hlt' <;> omega

end RankingOpinions
