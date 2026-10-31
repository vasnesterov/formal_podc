import Papers.PODC2011.LocallyCheckableProofs.Basic

/-!
# Labelled cycles

`cyc l lab mk` is the cycle through the (distinct) identifiers of the list `l`, in this order,
with node labels `lab` and with the edge from `x` to its successor in `l` marked iff `mk x`.

* `cyc_rotate`: rotating the list does not change the instance.
* `adj_cyc_interior`: an interior node `w[j]` of a prefix `w` of `l` has exactly the neighbours
  `w[j-1]`, `w[j+1]`.
* `viewEq_cyc_segment`: **the gluing lemma.** If two labelled cycles share a segment `w`, a node of
  `w` at distance `> r` from both ends of `w` has the same radius-`r` view in both, provided labels,
  marks and proofs agree near it.
-/

namespace Podc.LocallyCheckableProofs

open SimpleGraph Finset

variable {L : Type*}

/-- `y` follows `x` in the cyclic order of `l`. -/
def Succ (l : List ℕ) (x y : ℕ) : Prop :=
  ∃ (i : ℕ) (h : i < l.length), l[i] = x ∧ l[(i + 1) % l.length]'(Nat.mod_lt _ (by omega)) = y

/-- The labelled cycle on `l`. -/
def cyc (l : List ℕ) (lab : ℕ → L) (mk : ℕ → Bool) : Inst L where
  V := l.toFinset
  G := SimpleGraph.fromRel (Succ l)
  sub := by
    rintro u v ⟨-, ⟨i, hi, rfl, -⟩ | ⟨i, hi, -, rfl⟩⟩
    · simp
    · simp
  S := SimpleGraph.fromRel (fun x y => Succ l x y ∧ mk x = true)
  S_le := by
    intro x y h
    simp only [fromRel_adj] at h ⊢
    exact ⟨h.1, h.2.imp And.left And.left⟩
  lab := lab

@[simp] lemma cyc_V (l : List ℕ) (lab : ℕ → L) (mk : ℕ → Bool) : (cyc l lab mk).V = l.toFinset := rfl
@[simp] lemma cyc_lab (l : List ℕ) (lab : ℕ → L) (mk : ℕ → Bool) : (cyc l lab mk).lab = lab := rfl

lemma cyc_adj {l : List ℕ} {lab : ℕ → L} {mk : ℕ → Bool} {x y : ℕ} :
    (cyc l lab mk).G.Adj x y ↔ x ≠ y ∧ (Succ l x y ∨ Succ l y x) := by
  simp [cyc]

lemma cyc_sadj {l : List ℕ} {lab : ℕ → L} {mk : ℕ → Bool} {x y : ℕ} :
    (cyc l lab mk).S.Adj x y ↔
      x ≠ y ∧ ((Succ l x y ∧ mk x = true) ∨ (Succ l y x ∧ mk y = true)) := by
  simp [cyc]

/-! ### Rotation -/

lemma succ_rotate (l : List ℕ) (k : ℕ) (x y : ℕ) : Succ (l.rotate k) x y ↔ Succ l x y := by
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    have hl : 0 < l.length := by simp at hi; omega
    simp only [List.length_rotate] at hi ⊢
    refine ⟨(i + k) % l.length, Nat.mod_lt _ hl, ?_, ?_⟩
    · simp [List.getElem_rotate]
    · simp only [List.getElem_rotate]
      congr 1
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_mod ((i + 1) % _), Nat.mod_mod,
        ← Nat.add_mod]
      congr 1; ring
  · rintro ⟨i, hi, rfl, rfl⟩
    have hl : 0 < l.length := by omega
    have hm : (i + (l.length - k % l.length)) % l.length < (l.rotate k).length := by
      simp; exact Nat.mod_lt _ hl
    refine ⟨(i + (l.length - k % l.length)) % l.length, hm, ?_, ?_⟩
    · simp only [List.getElem_rotate]
      congr 1
      have := Nat.mod_lt k hl
      rw [Nat.mod_add_mod, show i + (l.length - k % l.length) + k
        = i + l.length * (1 + k / l.length) by
          have := Nat.mod_add_div k l.length; rw [Nat.mul_add]; omega]
      simp [Nat.mod_eq_of_lt hi]
    · simp only [List.getElem_rotate, List.length_rotate]
      congr 1
      have := Nat.mod_lt k hl
      rw [Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod, show i + (l.length - k % l.length) + (1 + k)
        = (i + 1) + l.length * (1 + k / l.length) by
          have := Nat.mod_add_div k l.length; rw [Nat.mul_add]; omega]
      simp

lemma cyc_rotate (l : List ℕ) (k : ℕ) (lab : ℕ → L) (mk : ℕ → Bool) :
    cyc (l.rotate k) lab mk = cyc l lab mk := by
  have hs : Succ (l.rotate k) = Succ l := by ext x y; exact succ_rotate l k x y
  ext x
  · simp [List.mem_rotate]
  · simp [cyc_adj, hs]
  · simp [cyc_sadj, hs]
  · rfl

/-- Swapping the two halves of the list does not change the cycle. -/
lemma cyc_append_comm (x y : List ℕ) (lab : ℕ → L) (mk : ℕ → Bool) :
    cyc (x ++ y) lab mk = cyc (y ++ x) lab mk := by
  rw [← List.rotate_append_length_eq, cyc_rotate]

/-! ### Interior nodes of a segment -/

lemma succ_interior_iff {w z : List ℕ} (h : (w ++ z).Nodup) {j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : j + 1 < w.length) (y : ℕ) :
    (Succ (w ++ z) w[j] y ↔ y = w[j + 1]) ∧ (Succ (w ++ z) y w[j] ↔ y = w[j - 1]) := by
  have hlen : (w ++ z).length = w.length + z.length := by simp
  have hw : ∀ (i : ℕ) (hi : i < w.length), (w ++ z)[i]'(by simp; omega) = w[i] := fun i hi => by
    simp [List.getElem_append_left hi]
  -- the position of `w[j]` in `w ++ z` is `j`
  have pos : ∀ (i : ℕ) (hi : i < (w ++ z).length), (w ++ z)[i] = w[j] → i = j := by
    intro i hi he
    rw [← hw j (by omega)] at he
    exact (List.Nodup.getElem_inj_iff h).1 he
  constructor
  · constructor
    · rintro ⟨i, hi, he, rfl⟩
      obtain rfl := pos i hi he
      simp only [Nat.mod_eq_of_lt (show i + 1 < (w ++ z).length by omega)]
      exact hw _ _
    · rintro rfl
      refine ⟨j, by omega, hw j (by omega), ?_⟩
      simp only [Nat.mod_eq_of_lt (show j + 1 < (w ++ z).length by omega)]
      exact hw _ _
  · constructor
    · rintro ⟨i, hi, rfl, he⟩
      have hi' : (i + 1) % (w ++ z).length = j := pos _ _ he
      have : i + 1 < (w ++ z).length := by
        by_contra hc
        have : i + 1 = (w ++ z).length := by omega
        rw [this, Nat.mod_self] at hi'; omega
      rw [Nat.mod_eq_of_lt this] at hi'
      subst hi'
      exact hw _ _
    · rintro rfl
      refine ⟨j - 1, by omega, hw _ (by omega), ?_⟩
      simp only [show j - 1 + 1 = j by omega, Nat.mod_eq_of_lt (show j < (w ++ z).length by omega)]
      exact hw j (by omega)

lemma adj_cyc_interior {w z : List ℕ} (h : (w ++ z).Nodup) {j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : j + 1 < w.length) {lab : ℕ → L} {mk : ℕ → Bool} (y : ℕ) :
    (cyc (w ++ z) lab mk).G.Adj w[j] y ↔ y = w[j + 1] ∨ y = w[j - 1] := by
  have hnd : w.Nodup := (List.nodup_append.1 h).1
  rw [cyc_adj, (succ_interior_iff h hj1 hj2 y).1, (succ_interior_iff h hj1 hj2 y).2]
  constructor
  · exact fun h => h.2
  · rintro (rfl | rfl)
    · refine ⟨fun he => ?_, Or.inl rfl⟩
      have := (List.Nodup.getElem_inj_iff hnd).1 he; omega
    · refine ⟨fun he => ?_, Or.inr rfl⟩
      have := (List.Nodup.getElem_inj_iff hnd).1 he; omega

lemma sadj_cyc_interior {w z : List ℕ} (h : (w ++ z).Nodup) {j : ℕ} (hj1 : 1 ≤ j)
    (hj2 : j + 1 < w.length) {lab : ℕ → L} {mk : ℕ → Bool} (y : ℕ) :
    (cyc (w ++ z) lab mk).S.Adj w[j] y ↔
      (y = w[j + 1] ∧ mk w[j] = true) ∨ (y = w[j - 1] ∧ mk w[j - 1] = true) := by
  have hnd : w.Nodup := (List.nodup_append.1 h).1
  rw [cyc_sadj, (succ_interior_iff h hj1 hj2 y).1, (succ_interior_iff h hj1 hj2 y).2]
  constructor
  · rintro ⟨-, (⟨rfl, hm⟩ | ⟨rfl, hm⟩)⟩
    · exact Or.inl ⟨rfl, hm⟩
    · exact Or.inr ⟨rfl, hm⟩
  · rintro (⟨rfl, hm⟩ | ⟨rfl, hm⟩)
    · refine ⟨fun he => ?_, Or.inl ⟨rfl, hm⟩⟩
      have := (List.Nodup.getElem_inj_iff hnd).1 he; omega
    · refine ⟨fun he => ?_, Or.inr ⟨rfl, hm⟩⟩
      have := (List.Nodup.getElem_inj_iff hnd).1 he; omega

/-- Nodes of the `r`-ball of an interior node `w[i]` (far from the ends of `w`) are `w[j]`,
`|j - i| ≤ r`. -/
lemma ball_cyc_segment {w z : List ℕ} (h : (w ++ z).Nodup) {lab : ℕ → L} {mk : ℕ → Bool}
    {i r : ℕ} (hi1 : r + 1 ≤ i) (hi2 : i + r + 1 < w.length) {x : ℕ}
    (hx : x ∈ ball (cyc (w ++ z) lab mk) w[i] r) :
    ∃ (j : ℕ) (hj : j < w.length), i ≤ j + r ∧ j ≤ i + r ∧ x = w[j] := by
  obtain ⟨p, hp⟩ := hx
  -- induction on the reversed walk
  have key : ∀ k u (q : (cyc (w ++ z) lab mk).G.Walk u w[i]), q.length = k → k ≤ r →
      ∃ (j : ℕ) (hj : j < w.length), i ≤ j + k ∧ j ≤ i + k ∧ u = w[j] := by
    intro k
    induction k with
    | zero =>
      intro u q hq _
      cases q with
      | nil => exact ⟨i, by omega, by omega, by omega, rfl⟩
      | cons _ _ => simp at hq
    | succ k ih =>
      intro u q hq hk
      cases q with
      | nil => simp at hq
      | @cons _ y _ ha q =>
        obtain ⟨j, hj, hj1, hj2, rfl⟩ := ih y q (by simp at hq; omega) (by omega)
        have := (adj_cyc_interior h (j := j) (by omega) (by omega) (lab := lab) (mk := mk) u).1
          ha.symm
        rcases this with hu | hu
        · exact ⟨j + 1, by omega, by omega, by omega, hu⟩
        · exact ⟨j - 1, by omega, by omega, by omega, hu⟩
  obtain ⟨j, hj, h1, h2, rfl⟩ := key p.length x p.reverse (by simp) hp
  exact ⟨j, hj, by omega, by omega, rfl⟩

/-- **Gluing lemma.** Two labelled cycles `w ++ z` and `w ++ z'` sharing the segment `w`: a node
`w[i]` at distance `> r` from both ends of `w` has the same radius-`r` view in both, if labels,
marks and proofs agree on `w[i-r-1], …, w[i+r]`. -/
lemma viewEq_cyc_segment {Λ : Type*} {w z z' : List ℕ} (h : (w ++ z).Nodup)
    (h' : (w ++ z').Nodup) {lab lab' : ℕ → L} {mk mk' : ℕ → Bool} {P P' : ℕ → Λ} {i r : ℕ}
    (hi1 : r + 1 ≤ i) (hi2 : i + r + 1 < w.length)
    (hag : ∀ (j : ℕ) (hj : j < w.length), i ≤ j + r + 1 → j ≤ i + r →
      lab w[j] = lab' w[j] ∧ mk w[j] = mk' w[j] ∧ P w[j] = P' w[j]) :
    ViewEq r (cyc (w ++ z) lab mk) P (cyc (w ++ z') lab' mk') P' w[i] := by
  apply viewEq_of_nbrs
  · intro x hx y
    obtain ⟨j, hj, hj1, hj2, rfl⟩ := ball_cyc_segment h hi1 hi2 hx
    rw [adj_cyc_interior h (by omega) (by omega), adj_cyc_interior h' (by omega) (by omega)]
  · intro x hx y
    obtain ⟨j, hj, hj1, hj2, rfl⟩ := ball_cyc_segment h hi1 hi2 hx
    rw [sadj_cyc_interior h (by omega) (by omega), sadj_cyc_interior h' (by omega) (by omega),
      (hag j hj (by omega) hj2).2.1, (hag (j - 1) (by omega) (by omega) (by omega)).2.1]
  · intro x hx
    obtain ⟨j, hj, hj1, hj2, rfl⟩ := ball_cyc_segment h hi1 hi2 hx
    simp [List.getElem_mem]
  · intro x hx
    obtain ⟨j, hj, hj1, hj2, rfl⟩ := ball_cyc_segment h hi1 hi2 hx
    exact (hag j hj (by omega) hj2).1
  · intro x hx
    obtain ⟨j, hj, hj1, hj2, rfl⟩ := ball_cyc_segment h hi1 hi2 hx
    exact (hag j hj (by omega) hj2).2.2

end Podc.LocallyCheckableProofs
