import Papers.PODC2015.MSTImpromptuRepair.Cut
import Cslib.Probability.Finite.Uniform

/-!
# `HP-TestOut`: set-equality testing by polynomial fingerprints (Section 2.2)

`HP-TestOut(x)` decides whether `E↑(T) ≠ E↓(T)` (Observation 1) by comparing the fingerprints
`𝒫(D)(α) = ∏_{e ∈ D} (α - edge_number(e))` over `ℤ_p` at a uniformly random `α`. The fingerprint of
`E↑(T)` is aggregated up the tree as a product of the local values `Local↑(y) = 𝒫(E↑(y))(α)`
(`fp_Eup_eq_prod_local`).

* `hpTestOut_false_of_no_cut` — if no edge leaves `T`, `HP-TestOut` always returns 0.
* `card_hpTestOut_fail_le` — if an edge leaves `T` and the dart numbers are distinct in `ℤ_p`,
  at most `D - 1` values of `α` make `HP-TestOut` return 0, where `D = |E↑(T)|` is the sum of the
  degrees of the vertices of `T` (the paper's `B`, "by summing up the degrees of nodes in `T`").
* `hpTestOut_error_lt` — **inequality (2)**: with `p > maxEdgeNum` and `p > D / ε`, the error
  probability is `< ε`.
* `fp_Eup_eq_fp_Edown_of_symm` — **the edge numbers must be ordered**: with the paper's literal
  edge number of an *undirected* edge ("concatenation of the IDs, smallest first"), the two
  fingerprints coincide for every `α`, so `HP-TestOut` never detects a leaving edge
  (`hpTestOut_symm_never`).
-/

namespace Podc.MSTImpromptuRepair

open Finset Polynomial Cslib.Probability

/-! ### Root counting for products of linear factors -/

section RootBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

-- CSLib candidate: Mathlib-style root bound (polynomial identity testing in one variable)
/-- Two different sets `A ≠ B` of the same size `D` have fingerprints `∏_{a ∈ A} (α - a)` and
`∏_{b ∈ B} (α - b)` that agree on at most `D - 1` points `α` (Schwartz–Zippel in one variable). -/
theorem card_prod_sub_eq_le {A B : Finset F} (hAB : A ≠ B) (hcard : #A = #B) :
    #(univ.filter fun α : F => ∏ a ∈ A, (α - a) = ∏ b ∈ B, (α - b)) ≤ #A - 1 := by
  set PA : F[X] := ∏ a ∈ A, (X - C a)
  set PB : F[X] := ∏ b ∈ B, (X - C b)
  have hPA : PA.Monic := monic_prod_of_monic A (fun a => X - C a) fun a _ => monic_X_sub_C a
  have hPB : PB.Monic := monic_prod_of_monic B (fun a => X - C a) fun b _ => monic_X_sub_C b
  have dA : PA.natDegree = #A := by
    simp only [PA]
    rw [natDegree_prod_of_monic A (fun a => X - C a) (fun a _ => monic_X_sub_C a)]
    simp
  have dB : PB.natDegree = #B := by
    simp only [PB]
    rw [natDegree_prod_of_monic B (fun a => X - C a) (fun a _ => monic_X_sub_C a)]
    simp
  have rA : PA.roots = A.val := by
    simp only [PA]; exact roots_prod_X_sub_C A
  have rB : PB.roots = B.val := by
    simp only [PB]; exact roots_prod_X_sub_C B
  have hQ : PA - PB ≠ 0 := by
    intro h
    apply hAB
    have : PA = PB := sub_eq_zero.1 h
    exact Finset.val_injective (by rw [← rA, ← rB, this])
  have hdeg : (PA - PB).natDegree < #A := by
    have hPA0 : PA ≠ 0 := hPA.ne_zero
    have hdegeq : PA.degree = PB.degree := by
      rw [degree_eq_natDegree hPA0, degree_eq_natDegree hPB.ne_zero, dA, dB, hcard]
    have hlt := degree_sub_lt hdegeq hPA0 (by rw [hPA.leadingCoeff, hPB.leadingCoeff])
    rw [degree_eq_natDegree hPA0, degree_eq_natDegree hQ, dA] at hlt
    exact_mod_cast hlt
  have hsub : univ.filter (fun α : F => ∏ a ∈ A, (α - a) = ∏ b ∈ B, (α - b)) ⊆
      (PA - PB).roots.toFinset := by
    intro α hα
    simp only [mem_filter, mem_univ, true_and] at hα
    rw [Multiset.mem_toFinset, mem_roots hQ, IsRoot, eval_sub, sub_eq_zero]
    simp [PA, PB, eval_prod, hα]
  calc _ ≤ #((PA - PB).roots.toFinset) := card_le_card hsub
    _ ≤ Multiset.card (PA - PB).roots := Multiset.toFinset_card_le _
    _ ≤ (PA - PB).natDegree := card_roots' _
    _ ≤ #A - 1 := by omega

end RootBound

/-! ### The fingerprint test -/

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (P : Sym2 V → Prop) [DecidablePred P]

/-- The fingerprint `𝒫(D)(α) = ∏_{d ∈ D} (α - num d) mod p` of a set of darts `D`, where
`num d ∈ ℕ` is the number of the dart `d`. -/
def fp {p : ℕ} (num : V × V → ℕ) (D : Finset (V × V)) (α : ZMod p) : ZMod p :=
  ∏ d ∈ D, (α - (num d : ZMod p))

/-- The value aggregated in the broadcast-and-echo of `HP-TestOut`: the product over the tree of
the local values `Local↑(y) = 𝒫(E↑(y))(α)` is `𝒫(E↑(T))(α)`. -/
theorem fp_Eup_eq_prod_local {p : ℕ} (num : V × V → ℕ) (T : Finset V) (α : ZMod p) :
    fp num (Eup G P T) α = ∏ y ∈ T, fp num (EupV G P y) α := by
  rw [fp, Eup_eq_biUnion, prod_biUnion (pairwiseDisjoint_EupV G P T)]; rfl

/-- Same for `E↓`. -/
theorem fp_Edown_eq_prod_local {p : ℕ} (num : V × V → ℕ) (T : Finset V) (α : ZMod p) :
    fp num (Edown G P T) α = ∏ y ∈ T, fp num (EdownV G P y) α := by
  rw [fp, Edown_eq_biUnion, prod_biUnion (pairwiseDisjoint_EdownV G P T)]; rfl

/-- The answer of `HP-TestOut(x)` (restricted to edges satisfying `P`, e.g. `weight ∈ [j, k]`)
for the random point `α`: "there is an edge leaving `T`" iff the fingerprints differ. -/
def hpTestOut {p : ℕ} (num : V × V → ℕ) (T : Finset V) (α : ZMod p) : Prop :=
  fp num (Eup G P T) α ≠ fp num (Edown G P T) α

instance {p : ℕ} (num : V × V → ℕ) (T : Finset V) : DecidablePred (hpTestOut G P (p := p) num T) :=
  fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-- `HP-TestOut` is always correct when no edge leaves `T`: it returns 0. -/
theorem hpTestOut_false_of_no_cut {p : ℕ} (num : V × V → ℕ) (T : Finset V)
    (h : ¬ ∃ e ∈ cut G T, P e) (α : ZMod p) : ¬ hpTestOut G P num T α := by
  rw [exists_cut_iff_Eup_ne_Edown, not_not] at h
  simp [hpTestOut, h]

/-- The darts of `G` (both orientations of every edge). -/
def darts : Finset (V × V) := univ.filter fun d => G.Adj d.1 d.2

theorem Eup_subset_darts (T : Finset V) : Eup G P T ⊆ darts G := by
  intro d; simp [Eup, darts]; tauto

theorem Edown_subset_darts (T : Finset V) : Edown G P T ⊆ darts G := by
  intro d; simp [Edown, darts]; tauto

variable {G P}

/-- **Error bound of `HP-TestOut`.** If an edge (satisfying `P`) leaves `T` and the dart numbers
are pairwise distinct modulo the prime `p`, then at most `|E↑(T)| - 1` of the `p` values of `α`
make `HP-TestOut` wrongly return 0. -/
theorem card_hpTestOut_fail_le {p : ℕ} [Fact p.Prime] (num : V × V → ℕ) (T : Finset V)
    (hinj : Set.InjOn (fun d => (num d : ZMod p)) (darts G))
    (hcut : ∃ e ∈ cut G T, P e) :
    #(univ.filter fun α : ZMod p => ¬ hpTestOut G P num T α) ≤ #(Eup G P T) - 1 := by
  have hne := (exists_cut_iff_Eup_ne_Edown G P T).1 hcut
  set f : V × V → ZMod p := fun d => (num d : ZMod p)
  have hiU : Set.InjOn f (Eup G P T) := hinj.mono (Eup_subset_darts G P T)
  have hiD : Set.InjOn f (Edown G P T) := hinj.mono (Edown_subset_darts G P T)
  have hA : #((Eup G P T).image f) = #(Eup G P T) := card_image_of_injOn hiU
  have hB : #((Edown G P T).image f) = #(Edown G P T) := card_image_of_injOn hiD
  have hAB : (Eup G P T).image f ≠ (Edown G P T).image f := by
    intro h
    apply hne
    ext d
    constructor
    · intro hd
      have : f d ∈ (Edown G P T).image f := h ▸ mem_image_of_mem f hd
      obtain ⟨d', hd', hfd⟩ := mem_image.1 this
      rwa [← hinj (Edown_subset_darts G P T hd') (Eup_subset_darts G P T hd) hfd]
    · intro hd
      have : f d ∈ (Eup G P T).image f := h.symm ▸ mem_image_of_mem f hd
      obtain ⟨d', hd', hfd⟩ := mem_image.1 this
      rwa [← hinj (Eup_subset_darts G P T hd') (Edown_subset_darts G P T hd) hfd]
  have key := card_prod_sub_eq_le hAB (by rw [hA, hB, card_Edown_eq_card_Eup])
  rw [hA] at key
  refine le_trans (le_of_eq ?_) key
  congr 1
  ext α
  simp only [mem_filter, mem_univ, true_and, hpTestOut, fp, not_not]
  rw [prod_image (fun x hx y hy h => hiU hx hy h), prod_image (fun x hx y hy h => hiD hx hy h)]

/-- **Inequality (2)** in probability form: `Pr_α[HP-TestOut returns 0] ≤ (D - 1)/p` with
`D = |E↑(T)|` (sum of the degrees in `T`), provided an edge leaves `T` and the dart numbers are
distinct modulo `p`. -/
theorem hpTestOut_fail_prob_le {p : ℕ} [Fact p.Prime] (num : V × V → ℕ) (T : Finset V)
    (hinj : Set.InjOn (fun d => (num d : ZMod p)) (darts G))
    (hcut : ∃ e ∈ cut G T, P e) :
    uprob (fun α : ZMod p => ¬ hpTestOut G P num T α) ≤ ((#(Eup G P T) : ℝ) - 1) / p := by
  classical
  rw [uprob_eq_card_filter, ZMod.card]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 := card_hpTestOut_fail_le num T hinj hcut
  have hD : 1 ≤ #(Eup G P T) := by
    obtain ⟨e, he, hP⟩ := hcut
    have := (exists_cut_iff_Eup_ne_Edown G P T).1 ⟨e, he, hP⟩
    by_contra h0
    apply this
    have h0' : Eup G P T = ∅ := card_eq_zero.1 (by omega)
    rw [h0', eq_comm, ← card_eq_zero, card_Edown_eq_card_Eup, h0', card_empty]
  gcongr
  have : ((#(Eup G P T) - 1 : ℕ) : ℝ) = (#(Eup G P T) : ℝ) - 1 := by push_cast [hD]; ring
  rw [← this]; exact_mod_cast h1

/-- **Inequality (2)** with the paper's choice of `p`: if the dart numbers are distinct naturals
below `p` (`p > maxEdgeNum`) and `p > D / ε` where `D = |E↑(T)|` is the sum of the degrees of the
nodes of `T`, then `Pr_α[P(E↑(T))(α) = P(E↓(T))(α)] < ε` whenever an edge leaves `T`. -/
theorem hpTestOut_error_lt {p : ℕ} [Fact p.Prime] (num : V × V → ℕ) (T : Finset V)
    (hinj : Set.InjOn num (darts G)) (hlt : ∀ d ∈ darts G, num d < p)
    {ε : ℝ} (hε : (#(Eup G P T) : ℝ) / ε < p) (hε0 : 0 < ε)
    (hcut : ∃ e ∈ cut G T, P e) :
    uprob (fun α : ZMod p => ¬ hpTestOut G P num T α) < ε := by
  have hinj' : Set.InjOn (fun d => (num d : ZMod p)) (darts G) := by
    intro a ha b hb h
    apply hinj ha hb
    have := (ZMod.natCast_eq_natCast_iff' (num a) (num b) p).1 h
    rwa [Nat.mod_eq_of_lt (hlt a ha), Nat.mod_eq_of_lt (hlt b hb)] at this
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine lt_of_le_of_lt (hpTestOut_fail_prob_le num T hinj' hcut) ?_
  rw [div_lt_iff₀ hp]
  rw [div_lt_iff₀ hε0] at hε
  nlinarith

/-- **Lower bound on the error.** Every dart with both endpoints in `T` lies in `E↑(T) ∩ E↓(T)`;
at its number both fingerprints vanish. So at least `|E↑(T) ∩ E↓(T)| = 2 · #(edges inside T)`
values of `α` are bad: the error bound `(D - 1)/p` needs `D` = the *sum of the degrees* (as in the
paper's step 0); with `B` = the number of edges incident to `T` (the paper's wording before (2)),
`p > B/ε` does not give error `< ε`. -/
theorem card_inter_le_card_hpTestOut_fail {p : ℕ} [NeZero p] (num : V × V → ℕ) (T : Finset V)
    (hinj : Set.InjOn (fun d => (num d : ZMod p)) (darts G)) :
    #(Eup G P T ∩ Edown G P T) ≤ #(univ.filter fun α : ZMod p => ¬ hpTestOut G P num T α) := by
  classical
  rw [← card_image_of_injOn (hinj.mono (fun d hd => Eup_subset_darts G P T (mem_inter.1 hd).1))]
  refine card_le_card fun α hα => ?_
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hα
  simp only [mem_filter, mem_univ, true_and, hpTestOut, not_not, fp]
  rw [prod_eq_zero (mem_inter.1 hd).1 (sub_self _), prod_eq_zero (mem_inter.1 hd).2 (sub_self _)]

/-! ### With unordered edge numbers the test is blind -/

variable (G P)

/-- If the number of a dart does not depend on its orientation (the paper's literal
`edge_number`: concatenation of the two IDs, smallest first), then `𝒫(E↑(T)) = 𝒫(E↓(T))`
identically, whatever `T`. -/
theorem fp_Eup_eq_fp_Edown_of_symm {p : ℕ} (num : V × V → ℕ) (hsymm : ∀ d, num d.swap = num d)
    (T : Finset V) (α : ZMod p) : fp num (Eup G P T) α = fp num (Edown G P T) α := by
  unfold fp
  refine prod_bij (fun d _ => d.swap) ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Edown, Eup, mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hd ⊢
    exact ⟨hd.1.symm, by rw [Sym2.eq_swap]; exact hd.2.1, hd.2.2⟩
  · intro a _ b _ h; simpa using h
  · intro d hd
    refine ⟨d.swap, ?_, by simp⟩
    simp only [Edown, Eup, mem_filter, mem_univ, true_and, Prod.fst_swap, Prod.snd_swap] at hd ⊢
    exact ⟨hd.1.symm, by rw [Sym2.eq_swap]; exact hd.2.1, hd.2.2⟩
  · intro d _; rw [hsymm]

/-- Consequently, with orientation-independent edge numbers `HP-TestOut` returns 0 for every `α`,
even when edges leave `T`. -/
theorem hpTestOut_symm_never {p : ℕ} (num : V × V → ℕ) (hsymm : ∀ d, num d.swap = num d)
    (T : Finset V) (α : ZMod p) : ¬ hpTestOut G P num T α := by
  simp [hpTestOut, fp_Eup_eq_fp_Edown_of_symm G P num hsymm]

end Podc.MSTImpromptuRepair
