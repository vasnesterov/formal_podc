import Mathlib

/-!
# The safe area `Γ` and Lemma 1 of Vaidya–Garg (PODC 2013)

`Γ(Y) = ⋂_{T ⊆ Y, |T| = |Y| - f} H(T)` (equation (1) of the paper), where `H` is the convex hull.
A multiset `Y` of points is represented by an indexed family `y : ι → E` restricted to a finite set
of indices `C` (Appendix B of the paper defines multiset subsets exactly through index sets).

* `GammaOn f C y` — `Γ` of the multiset `{y k | k ∈ C}`.
* `GammaOn_nonempty` — **Lemma 1**: if `|C| ≥ (dim E + 1) f + 1` then `Γ ≠ ∅`.
  The paper derives it from Tverberg's theorem; we derive it from **Helly's theorem**
  (`Convex.helly_theorem'` in Mathlib) and a counting argument: any `dim E + 1` of the sets
  `T` miss together at most `(dim E + 1) f < |C|` indices, so they share a point of `Y`.
* `GammaOn_subset_convexHull` — `Γ` is contained in the hull of every sub-multiset with at least
  `|C| - f` elements (used for validity).
* `gammaPt` — a deterministic choice of a point of `Γ` that depends only on the multiset.
* `lbPoint`, `eq_lbPoint_of_mem_convexHull` — the point configuration of the lower-bound proofs
  (Theorems 1 and 4) and the fact that it pins down every valid decision.
* `gamma_empty_of_card_eq` — Lemma 1 is tight: `Γ` can be empty when `|Y| = (d + 1) f`.
-/

open Finset Module
open scoped Pointwise

namespace ByzantineVectorConsensus

section Gamma

variable {ι E : Type*} [AddCommGroup E] [Module ℝ E]

-- CSLib candidate (`GammaOn` and Lemma 1 via Helly)
/-- `Γ` (equation (1) of the paper) of the multiset `{y k | k ∈ C}`: the intersection of the
convex hulls of all sub-multisets of size `|C| - f`. -/
def GammaOn (f : ℕ) (C : Finset ι) (y : ι → E) : Set E :=
  ⋂ T ∈ C.powersetCard (C.card - f), convexHull ℝ (y '' (T : Set ι))

theorem mem_GammaOn {f : ℕ} {C : Finset ι} {y : ι → E} {z : E} :
    z ∈ GammaOn f C y ↔ ∀ T ⊆ C, T.card = C.card - f → z ∈ convexHull ℝ (y '' (T : Set ι)) := by
  simp [GammaOn, mem_powersetCard]

/-- `Γ` only depends on the multiset `{y k | k ∈ C}`. -/
theorem GammaOn_congr {f : ℕ} {C : Finset ι} {y y' : ι → E} (h : ∀ k ∈ C, y k = y' k) :
    GammaOn f C y = GammaOn f C y' := by
  ext z
  simp only [mem_GammaOn]
  refine forall₂_congr fun T hT => imp_congr_right fun _ => ?_
  rw [Set.image_congr fun k hk => h k (hT hk)]

/-- `Γ` is contained in the convex hull of every sub-multiset with at least `|C| - f` elements. -/
theorem GammaOn_subset_convexHull {f : ℕ} {C T : Finset ι} {y : ι → E} (hT : T ⊆ C)
    (hcard : C.card - f ≤ T.card) :
    GammaOn f C y ⊆ convexHull ℝ (y '' (T : Set ι)) := by
  obtain ⟨T', hT'T, hT'card⟩ := exists_subset_card_eq hcard
  intro z hz
  exact convexHull_mono (Set.image_mono (by exact_mod_cast hT'T))
    (mem_GammaOn.1 hz T' (hT'T.trans hT) hT'card)

/-- **Lemma 1** of the paper: for a multiset of at least `(d + 1) f + 1` points in a
`d`-dimensional real vector space, `Γ` is nonempty. Proved via Helly's theorem (the paper uses
Tverberg's theorem). -/
theorem GammaOn_nonempty [FiniteDimensional ℝ E] {f : ℕ} {C : Finset ι} (y : ι → E)
    (hC : (finrank ℝ E + 1) * f < C.card) : (GammaOn f C y).Nonempty := by
  classical
  unfold GammaOn
  refine Convex.helly_theorem' (fun T _ => convex_convexHull ℝ _) fun I hI hIcard => ?_
  -- the indices missed by some member of `I`
  set miss := I.biUnion fun T => C \ T
  have hmiss : miss.card < C.card := by
    calc miss.card ≤ ∑ T ∈ I, (C \ T).card := card_biUnion_le
      _ ≤ ∑ _T ∈ I, f := by
          refine sum_le_sum fun T hT => ?_
          have hT := mem_powersetCard.1 (hI hT)
          rw [card_sdiff_of_subset hT.1, hT.2]
          omega
      _ = I.card * f := by simp
      _ ≤ (finrank ℝ E + 1) * f := Nat.mul_le_mul_right _ hIcard
      _ < C.card := hC
  obtain ⟨k, hkC, hkmiss⟩ : ∃ k ∈ C, k ∉ miss := by
    by_contra h
    push Not at h
    exact absurd (card_le_card fun k hk => h k hk) (by omega)
  refine ⟨y k, Set.mem_iInter₂.2 fun T hT => subset_convexHull ℝ _ ⟨k, ?_, rfl⟩⟩
  by_contra hkT
  exact hkmiss (mem_biUnion.2 ⟨T, hT, mem_sdiff.2 ⟨hkC, hkT⟩⟩)

/-- A deterministic choice of a point of a set (`0` if the set is empty). -/
noncomputable def pickPt (X : Set E) : E := by
  classical
  exact if h : X.Nonempty then h.some else 0

omit [Module ℝ E] in
theorem pickPt_mem {X : Set E} (h : X.Nonempty) : pickPt X ∈ X := by
  classical
  simp only [pickPt, h, ↓reduceDIte]
  exact h.some_mem

/-- The point of `Γ` chosen (identically by all processes) in Step 2 of the algorithms. It only
depends on the multiset `{y k | k ∈ C}` (`gammaPt_congr`). -/
noncomputable def gammaPt (f : ℕ) (C : Finset ι) (y : ι → E) : E := pickPt (GammaOn f C y)

theorem gammaPt_congr {f : ℕ} {C : Finset ι} {y y' : ι → E} (h : ∀ k ∈ C, y k = y' k) :
    gammaPt f C y = gammaPt f C y' := by
  rw [gammaPt, gammaPt, GammaOn_congr h]

theorem gammaPt_mem [FiniteDimensional ℝ E] {f : ℕ} {C : Finset ι} (y : ι → E)
    (hC : (finrank ℝ E + 1) * f < C.card) : gammaPt f C y ∈ GammaOn f C y :=
  pickPt_mem (GammaOn_nonempty y hC)

end Gamma

/-! ### The point configuration of the lower bounds -/

section LowerBoundPoints

variable {d : ℕ}

/-- The input of a process with label `l` in the lower-bound constructions: label `0` (and every
label `> d`) gets the origin, label `l ∈ [1, d]` gets `c • e_{l-1}`. -/
def lbPoint (d : ℕ) (c : ℝ) (l : ℕ) : Fin d → ℝ := fun i => if i.val + 1 = l then c else 0

/-- **Pinning lemma.** If `z` lies, for every label `l ≤ d` other than `m₀ ≤ d`, in the convex hull
of the points with labels `≠ l` (and `≤ d`), then `z` is the point with label `m₀`. This is the
geometric core of the proofs of Theorems 1 and 4. -/
theorem eq_lbPoint_of_mem_convexHull {c : ℝ} {z : Fin d → ℝ} {m₀ : ℕ} (hm₀ : m₀ ≤ d)
    (h : ∀ l ≤ d, l ≠ m₀ → z ∈ convexHull ℝ (lbPoint d c '' {m | m ≠ l ∧ m ≤ d})) :
    z = lbPoint d c m₀ := by
  -- coordinate `i` vanishes when `i + 1 ≠ m₀`
  have hcoord : ∀ i : Fin d, i.val + 1 ≠ m₀ → z i = 0 := by
    intro i hi
    have hz := h (i.val + 1) (by omega) hi
    have hsub : lbPoint d c '' {m | m ≠ i.val + 1 ∧ m ≤ d} ⊆ {w : Fin d → ℝ | w i = 0} := by
      rintro _ ⟨m, ⟨hm, -⟩, rfl⟩
      simp [lbPoint, Ne.symm hm]
    have hconv : Convex ℝ {w : Fin d → ℝ | w i = 0} :=
      convex_hyperplane (f := fun w : Fin d → ℝ => w i) ⟨fun _ _ => rfl, fun _ _ => rfl⟩ 0
    exact convexHull_min hsub hconv hz
  funext i
  by_cases hi : i.val + 1 = m₀
  · -- use the constraint for label `0`: the coordinates sum to `c`
    have hm0 : m₀ ≠ 0 := by omega
    have hz := h 0 (Nat.zero_le _) (Ne.symm hm0)
    have hsub : lbPoint d c '' {m | m ≠ 0 ∧ m ≤ d} ⊆ {w : Fin d → ℝ | ∑ j, w j = c} := by
      rintro _ ⟨m, ⟨hm, hmd⟩, rfl⟩
      simp only [lbPoint, Set.mem_ofPred_eq]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
      have : (univ.filter fun j : Fin d => j.val + 1 = m) = {⟨m - 1, by omega⟩} := by
        ext j; simp [Fin.ext_iff]; omega
      simp [this]
    have hconv : Convex ℝ {w : Fin d → ℝ | ∑ j, w j = c} :=
      convex_hyperplane (f := fun w : Fin d → ℝ => ∑ j, w j)
        ⟨fun _ _ => by simp [Finset.sum_add_distrib], fun _ _ => by simp [Finset.mul_sum]⟩ c
    have hsum : ∑ j, z j = c := convexHull_min hsub hconv hz
    rw [← Finset.add_sum_erase _ _ (mem_univ i)] at hsum
    have : ∑ j ∈ univ.erase i, z j = 0 :=
      Finset.sum_eq_zero fun j hj => hcoord j (by
        have := (mem_erase.1 hj).1; intro h'; exact this (Fin.ext (by omega)))
    simp [lbPoint, hi, ← hsum, this]
  · simp [lbPoint, hi, hcoord i hi]

/-- Translated version of `eq_lbPoint_of_mem_convexHull` (inputs `a + lbPoint d c l`). -/
theorem eq_add_lbPoint_of_mem_convexHull {a : Fin d → ℝ} {c : ℝ} {z : Fin d → ℝ} {m₀ : ℕ}
    (hm₀ : m₀ ≤ d)
    (h : ∀ l ≤ d, l ≠ m₀ →
      z ∈ convexHull ℝ ((fun m => a + lbPoint d c m) '' {m | m ≠ l ∧ m ≤ d})) :
    z = a + lbPoint d c m₀ := by
  have key : z - a = lbPoint d c m₀ := by
    refine eq_lbPoint_of_mem_convexHull hm₀ fun l hl hlm => ?_
    have hz := h l hl hlm
    have himg : (fun m => a + lbPoint d c m) '' {m | m ≠ l ∧ m ≤ d} =
        a +ᵥ (lbPoint d c '' {m | m ≠ l ∧ m ≤ d}) := by
      rw [← Set.image_vadd, Set.image_image]; rfl
    rw [himg, convexHull_vadd] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    simpa [vadd_eq_add] using hw
  rw [← key]; abel

theorem lbPoint_apply_zero_ne {c : ℝ} (hd : 1 ≤ d) :
    lbPoint d c 1 ⟨0, hd⟩ - lbPoint d c 0 ⟨0, hd⟩ = c := by
  simp [lbPoint]

end LowerBoundPoints

/-! ### Tightness of Lemma 1 -/

/-- Lemma 1 is tight: for `f ≥ 1` there are `(d + 1) f` points in `ℝ^d` whose `Γ` is empty
(`f` copies of the origin and of each `e_i`). This is the content of the proof of Theorem 1. -/
theorem gamma_empty_of_card_eq (d f : ℕ) (hf : 1 ≤ f) :
    GammaOn f (univ : Finset (Fin ((d + 1) * f))) (fun k => lbPoint d 1 (k.val / f)) = ∅ := by
  set y : Fin ((d + 1) * f) → Fin d → ℝ := fun k => lbPoint d 1 (k.val / f)
  have hlab : ∀ k : Fin ((d + 1) * f), k.val / f ≤ d := fun k => by
    have := k.isLt
    have : k.val / f < d + 1 := Nat.div_lt_of_lt_mul (by linarith [mul_comm (d + 1) f])
    omega
  -- the processes with label `l`
  have hcls : ∀ l ≤ d, ((univ : Finset (Fin ((d + 1) * f))).filter fun k => k.val / f = l).card
      = f := by
    intro l hl
    refine (card_bij (t := range f) (fun k _ => k.val - l * f) (fun k hk => ?_)
      (fun a ha b hb hab => ?_) (fun j hj => ?_)).trans (card_range f)
    · simp only [mem_filter, mem_univ, true_and] at hk
      simp only [mem_range]
      have h1 := Nat.lt_div_mul_add (a := k.val) (b := f) (by omega)
      have h2 := Nat.div_mul_le_self k.val f
      rw [hk] at h1 h2
      omega
    · simp only [mem_filter, mem_univ, true_and] at ha hb
      have h1 := Nat.div_mul_le_self a.val f
      have h2 := Nat.div_mul_le_self b.val f
      rw [ha] at h1; rw [hb] at h2
      exact Fin.ext (by omega)
    · simp only [mem_range] at hj
      have hlt : l * f + j < (d + 1) * f := by nlinarith
      refine ⟨⟨l * f + j, hlt⟩, ?_, by simp⟩
      simp only [mem_filter, mem_univ, true_and]
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj]
      simp
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hz
  -- `z` is pinned to label `0` and to label `1`
  have key : ∀ m₀ ≤ d, z = lbPoint d 1 m₀ := by
    intro m₀ hm₀
    refine eq_lbPoint_of_mem_convexHull hm₀ fun l hl _ => ?_
    set T := (univ : Finset (Fin ((d + 1) * f))).filter fun k => k.val / f ≠ l
    have hT : T.card = (d + 1) * f - f := by
      have := card_filter_add_card_filter_not
        (s := (univ : Finset (Fin ((d + 1) * f)))) (fun k => k.val / f = l)
      simp only [card_univ, Fintype.card_fin] at this
      rw [hcls l hl] at this
      simp only [T, ne_eq]
      omega
    have := mem_GammaOn.1 hz T (subset_univ _) (by simp [hT])
    refine convexHull_mono ?_ this
    rintro _ ⟨k, hk, rfl⟩
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, T] at hk
    exact ⟨k.val / f, ⟨hk, hlab k⟩, rfl⟩
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- `d = 0`: `Γ` is the hull of the `f`-element sub-multisets of `f` points: the multiset
    -- itself must be dropped entirely, and the hull of the empty set is empty
    have := mem_GammaOn.1 hz ∅ (empty_subset _) (by simp)
    simp at this
  · have h0 := key 0 (Nat.zero_le _)
    have h1 := key 1 hd
    have := congrFun (h0.symm.trans h1) ⟨0, hd⟩
    simp [lbPoint] at this

end ByzantineVectorConsensus
