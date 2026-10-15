import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Fin.Basic

/-!
# Weights of brakets and cyclic successors

Breitkopf, Dallot, El-Hayek, Schmid, *Ranking Opinions with Few States in Population Protocols*,
PODC 2026 (arXiv:2605.18707), Section 3.1.

The weight of the braket `⟨i|j⟩` is `k` if `i = j` and `(j - i) mod k` otherwise (the clockwise
distance from `i` to `j` on the modular clock).
-/

namespace RankingOpinions

variable {k : ℕ}

/-- A braket `⟨i|j⟩`: bra `i` (first component) and ket `j` (second component). -/
abbrev Braket (k : ℕ) := Fin k × Fin k

/-- The weight of `⟨i|j⟩` (Section 3.1): `k` if `i = j`, `(j - i) mod k` otherwise.
We use an explicit natural-number formula; `w_eq_sub` shows it agrees with the paper's. -/
def w (k : ℕ) (i j : Fin k) : ℕ :=
  if i = j then k else if i.val < j.val then j.val - i.val else j.val + k - i.val

/-- The weight agrees with the paper's definition `(j - i) mod k` (Fin subtraction is modular). -/
lemma w_val (i j : Fin k) : w k i j =
    if i.val = j.val then k else if i.val < j.val then j.val - i.val else j.val + k - i.val := by
  simp [w, Fin.ext_iff]

/-- The weight agrees with the paper's definition `(j - i) mod k` (Fin subtraction is modular). -/
lemma w_eq_sub (i j : Fin k) : w k i j = if i = j then k else (j - i : Fin k).val := by
  have := i.isLt; have := j.isLt
  rw [w_val, Fin.sub_def]
  simp only [Fin.ext_iff]
  split_ifs with h1 h2
  · rfl
  · have : k - i.val + j.val = (j.val - i.val) + k := by omega
    simp only [this, Nat.add_mod_right, Nat.mod_eq_of_lt (show j.val - i.val < k by omega)]
  · simp only [Nat.mod_eq_of_lt (show k - i.val + j.val < k by omega)]
    omega

lemma w_self (i : Fin k) : w k i i = k := by simp [w]

lemma w_le (i j : Fin k) : w k i j ≤ k := by
  rw [w_val]; split_ifs <;> omega

lemma w_lt_of_ne {i j : Fin k} (h : i ≠ j) : w k i j < k := by
  have := Fin.val_ne_of_ne h
  have := i.isLt; have := j.isLt
  rw [w_val]; split_ifs <;> omega

lemma w_pos (i j : Fin k) : 0 < w k i j := by
  have := i.isLt; have := j.isLt
  rw [w_val]; split_ifs <;> omega

/-- `w i ·` is injective. -/
lemma w_inj {i j j' : Fin k} (h : w k i j = w k i j') : j = j' := by
  have := i.isLt; have := j.isLt; have := j'.isLt
  rw [w_val, w_val] at h
  apply Fin.ext
  split_ifs at h <;> omega

/-- Key geometric fact: if `h` is closer clockwise to `g` than `i` is (`w g h < w g i`) and
`i ≠ g`, then `i` is farther from `h` (clockwise to `h`) than `g` is. -/
lemma w_lt_w_of_closer {g h i : Fin k} (hig : i ≠ g) (hgi : w k g h < w k g i) :
    w k g h < w k i h := by
  have := g.isLt; have := h.isLt; have := i.isLt
  have hig' : i.val ≠ g.val := Fin.val_ne_of_ne hig
  rw [w_val, w_val] at hgi ⊢
  split_ifs at hgi ⊢ <;> omega

/-! ## Cyclic successor within a set of colors -/

/-- The cyclic successor of `g` in `G`: the element `h ∈ G` minimizing `w g h`
(this is `g` itself iff `G = {g}`). -/
noncomputable def nxt (G : Finset (Fin k)) (g : Fin k) : Fin k :=
  if hG : G.Nonempty then (G.exists_min_image (w k g) hG).choose else g

lemma nxt_mem {G : Finset (Fin k)} {g : Fin k} (hg : g ∈ G) : nxt G g ∈ G := by
  have hG : G.Nonempty := ⟨g, hg⟩
  simp only [nxt, hG, dite_true]
  exact (G.exists_min_image (w k g) hG).choose_spec.1

lemma nxt_min {G : Finset (Fin k)} {g : Fin k} (hg : g ∈ G) {h : Fin k} (hh : h ∈ G) :
    w k g (nxt G g) ≤ w k g h := by
  have hG : G.Nonempty := ⟨g, hg⟩
  simp only [nxt, hG, dite_true]
  exact (G.exists_min_image (w k g) hG).choose_spec.2 h hh

lemma nxt_lt {G : Finset (Fin k)} {g : Fin k} (hg : g ∈ G) {h : Fin k} (hh : h ∈ G)
    (hne : h ≠ nxt G g) : w k g (nxt G g) < w k g h :=
  lt_of_le_of_ne (nxt_min hg hh) (fun e => hne (w_inj e).symm)

lemma nxt_eq_self_iff {G : Finset (Fin k)} {g : Fin k} (hg : g ∈ G) : nxt G g = g ↔ G = {g} := by
  constructor
  · intro h
    ext h'
    simp only [Finset.mem_singleton]
    refine ⟨fun hh' => ?_, fun e => e ▸ hg⟩
    by_contra hne
    have := nxt_min hg hh'
    rw [h, w_self] at this
    exact absurd (w_lt_of_ne (Ne.symm hne)) (not_lt.2 this)
  · intro hG
    have := nxt_mem (G := G) hg
    rw [hG, Finset.mem_singleton] at this
    subst hG; exact this

/-- `nxt G` is injective on `G`. -/
lemma nxt_injOn (G : Finset (Fin k)) : Set.InjOn (nxt G) G := by
  intro g1 hg1 g2 hg2 he
  by_contra hne
  set h := nxt G g1 with hh
  have hh2 : nxt G g2 = h := he.symm
  -- `g2` is not closer to `g1` than `h`, and vice versa
  have hmem : h ∈ G := nxt_mem hg1
  have h1 : h ≠ g1 := by
    intro e
    have := (nxt_eq_self_iff (G := G) hg1).1 (by rw [← hh, e])
    rw [this] at hg2; exact hne (Finset.mem_singleton.1 hg2).symm
  have h2 : h ≠ g2 := by
    intro e
    have := (nxt_eq_self_iff (G := G) hg2).1 (by rw [hh2, e])
    rw [this] at hg1; exact hne (Finset.mem_singleton.1 hg1)
  -- `w g1 h < w g1 g2` since `g2 ≠ h`
  have a1 : w k g1 h < w k g1 g2 := nxt_lt (G := G) hg1 (by exact_mod_cast hg2) (Ne.symm h2)
  have a2 : w k g2 h < w k g2 g1 := hh2 ▸ nxt_lt (G := G) hg2 (by exact_mod_cast hg1) (hh2 ▸ Ne.symm h1)
  have := w_lt_w_of_closer (fun e => hne e.symm) a1
  -- now `w g1 h < w g2 h`; combine with a2 for a contradiction
  have := g1.isLt; have := g2.isLt; have := h.isLt
  have v1 := Fin.val_ne_of_ne h1; have v2 := Fin.val_ne_of_ne h2
  have v3 : g1.val ≠ g2.val := Fin.val_ne_of_ne hne
  rw [w_val, w_val] at *
  split_ifs at * <;> omega

lemma nxt_image (G : Finset (Fin k)) : G.image (nxt G) = G := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hx
    exact nxt_mem hg
  · rw [Finset.card_image_of_injOn (nxt_injOn G)]

end RankingOpinions
