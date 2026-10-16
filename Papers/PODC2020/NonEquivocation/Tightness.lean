import Papers.PODC2020.NonEquivocation.PSL

/-!
# Theorem 6.1 (tightness of `n > 2t`) — corrected — and the exact solvability threshold

Madsen–Debois, PODC 2020, Section 6.

Theorem 6.1 claims: for every number of rounds `k` and `n ≤ 2t`, no deterministic algorithm solves
interactive consistency in the weak non-equivocation fault model. This is **false for `n ≤ 3`**
(`theorem_6_1_false_n2`, `theorem_6_1_false_n3`): if at most one process is non-faulty there is
nothing to agree on, so for `n = 2, t = 1` and `n = 3, t = 2` the problem reduces to `t = 0`, resp.
`t = 1`, which Algorithm 2 solves. The paper's proof needs four non-empty groups `O, Q, R, S`
("WLOG `n = 2t`", groups of size `t/2`), i.e. `n ≥ 4`.

For `n ≥ 4` the statement holds, with the paper's four runs (`not_solvesIC_of_groups`,
`theorem_6_1`). We construct the runs as an `ExecSys` with four worlds in which every faulty group
imitates the non-faulty behaviour of the same group in another world (so nobody equivocates), and
`O` omits towards `S` in runs 3 and 4. The precise threshold is `icSolvable_wne_iff`:
interactive consistency is solvable under weak non-equivocation iff `n > 2t` or `n ≤ 3`.
-/

namespace NonEquivocation

open Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] [OmitVal V]

namespace Tight

/-- Faulty groups in the four runs (groups `0 = O`, `1 = Q`, `2 = R`, `3 = S`; worlds `0..3` are the
paper's runs 1..4): run 1: `R, S`; run 2: `Q, S`; run 3: `O, R`; run 4: `O, Q`. -/
def faultyT (w a : Fin 4) : Bool :=
  match w, a with
  | 0, 2 | 0, 3 | 1, 1 | 1, 3 | 2, 0 | 2, 2 | 3, 0 | 3, 1 => true
  | _, _ => false

/-- Which world a group imitates. -/
def nbT (w a : Fin 4) : Fin 4 :=
  match w, a with
  | 0, 2 => 3 | 0, 3 => 2
  | 1, 1 => 2 | 1, 3 => 3
  | 2, 0 => 0 | 2, 2 => 3
  | 3, 0 => 1 | 3, 1 => 2
  | w, _ => w

/-- `O` omits everything towards `S` in runs 3 and 4. -/
def omT (w b a : Fin 4) : Bool := b = 0 && a = 3 && (w = 2 || w = 3)

/-- Indistinguishability of worlds for a member of group `a`: `Q` cannot distinguish runs 1 and 3,
`R` runs 2 and 4, `S` runs 3 and 4. -/
def relT (w w' a : Fin 4) : Bool :=
  w = w' || (a = 1 && ((w = 0 && w' = 2) || (w = 2 && w' = 0))) ||
    (a = 2 && ((w = 1 && w' = 3) || (w = 3 && w' = 1))) ||
    (a = 3 && ((w = 2 && w' = 3) || (w = 3 && w' = 2)))

lemma honestT : ∀ w a : Fin 4, faultyT w a = false → nbT w a = w ∧ ∀ b, omT w a b = false := by
  decide

lemma closedT : ∀ w w' a b : Fin 4, relT w w' a = true →
    (omT w b a = omT w' b a) ∧
      (omT w b a = false → nbT w b = nbT w' b ∨ relT (nbT w b) (nbT w' b) b = true) := by
  decide

lemma relT_input : ∀ w w' : Fin 4, relT w w' 0 = true → w = w' := by decide

/-- The four runs. -/
def sys (g : P → Fin 4) (src : P) (v u : V) : ExecSys (Fin 4) P V where
  input w y := if y = src then some (if w = 0 ∨ w = 2 then v else u) else some v
  nb w y := nbT w (g y)
  om w _ y x := omT w (g y) (g x) = true

/-- The faulty set of a run. -/
def Fw (g : P → Fin 4) (w : Fin 4) : Finset P := univ.filter fun x => faultyT w (g x) = true

end Tight

open Tight in
/-- **Theorem 6.1** (core): given a partition of the processes into four non-empty groups
`O ∋ src, Q, R, S` such that the faulty sets of the paper's four runs (`R ∪ S`, `Q ∪ S`, `O ∪ R`,
`O ∪ Q`) have at most `t` elements, no algorithm solves interactive consistency under weak
non-equivocation, for any number of rounds `k`. -/
theorem not_solvesIC_of_groups [Nontrivial V] (g : P → Fin 4) (src : P) (hsrc : g src = 0)
    {q r s : P} (hq : g q = 1) (hr : g r = 2) (hs : g s = 3) {t : ℕ}
    (hcard : ∀ w, (Fw g w).card ≤ t) (k : ℕ) (A : Alg P V) : ¬ SolvesIC wne k t A := by
  intro hA
  obtain ⟨v, u, hvu⟩ := exists_pair_ne V
  let E := sys g src v u
  have honest : ∀ w, E.Honest w (Fw g w) := by
    intro w y hy
    have hf : faultyT w (g y) = false := by simpa [Fw] using hy
    obtain ⟨h1, h2⟩ := honestT w (g y) hf
    exact ⟨h1, fun _ x => by simp [E, sys, h2]⟩
  have spec : ∀ w, _ := fun w => hA (Fw g w) (E.σ w) (hcard w) (E.wne_of (honest w) k)
    (fun y _ => by simp only [ExecSys.σ_single, E, sys]; split_ifs <;> simp)
  -- indistinguishability
  have bisim : E.IsBisim fun w w' x => relT w w' (g x) = true := by
    intro w w' x hx
    refine ⟨?_, fun y _ => ?_⟩
    · by_cases hxs : x = src
      · subst hxs; rw [hsrc] at hx; rw [relT_input w w' hx]
      · simp [E, sys, hxs]
    · obtain ⟨h1, h2⟩ := closedT w w' (g x) (g y) hx
      refine ⟨by simp [E, sys, h1], fun hno => ?_⟩
      exact h2 (by simpa [E, sys] using hno)
  have view_eq : ∀ w w' x, relT w w' (g x) = true → view k (E.σ w) x = view k (E.σ w') x :=
    fun w w' x h => E.view_eq_of_rel bisim h k
  have corr : ∀ w x, faultyT w (g x) = false → x ∉ Fw g w := fun w x h => by simp [Fw, h]
  -- run 1: `Q` decides `v`; run 3: so does `S`
  have h1 : A q (view k (E.σ 0) q) src = v := by
    have := (spec 0).1 q src (corr 0 q (by rw [hq]; decide)) (corr 0 src (by rw [hsrc]; decide))
    simp [E, sys] at this; exact this.symm
  have h3 : A s (view k (E.σ 2) s) src = v := by
    rw [(spec 2).2 s q src (corr 2 s (by rw [hs]; decide)) (corr 2 q (by rw [hq]; decide)),
      ← view_eq 0 2 q (by rw [hq]; decide), h1]
  -- run 2: `R` decides `u`; run 4: so does `S`
  have h2 : A r (view k (E.σ 1) r) src = u := by
    have := (spec 1).1 r src (corr 1 r (by rw [hr]; decide)) (corr 1 src (by rw [hsrc]; decide))
    simp [E, sys] at this; exact this.symm
  have h4 : A s (view k (E.σ 3) s) src = u := by
    rw [(spec 3).2 s r src (corr 3 s (by rw [hs]; decide)) (corr 3 r (by rw [hr]; decide)),
      ← view_eq 1 3 r (by rw [hr]; decide), h2]
  -- `S` cannot distinguish runs 3 and 4
  rw [view_eq 2 3 s (by rw [hs]; decide)] at h3
  exact hvu (h3.symm.trans h4)

omit [DecidableEq P] in
open Tight in
lemma card_Fw (g : P → Fin 4) (w : Fin 4) :
    (Fw g w).card = ∑ c : Fin 4, if faultyT w c then (univ.filter fun x => g x = c).card else 0 := by
  rw [Fw, Finset.card_eq_sum_card_fiberwise (f := g) (t := univ) (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.filter_filter]
  split_ifs with h
  · congr 1; ext x; simp only [mem_filter, mem_univ, true_and]
    constructor
    · exact fun h' => h'.2
    · intro h'; subst h'; exact ⟨h, rfl⟩
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x - ⟨h1, rfl⟩; exact h h1

open Tight in
/-- **Theorem 6.1** (corrected): for `4 ≤ n ≤ 2t` and any number of rounds `k`, no algorithm solves
interactive consistency in the weak non-equivocation fault model. -/
theorem theorem_6_1 [Nontrivial V] {t : ℕ} (h4 : 4 ≤ Fintype.card P)
    (h : Fintype.card P ≤ 2 * t) (k : ℕ) (A : Alg P V) : ¬ SolvesIC wne k t A := by
  set n := Fintype.card P with hn
  obtain ⟨src⟩ : Nonempty P := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨s, hs⟩ := Fintype.exists_ne_of_one_lt_card (by omega) src
  set rest := (univ : Finset P) \ {src, s} with hrest
  have hcrest : rest.card = n - 2 := by
    rw [hrest, Finset.card_sdiff_of_subset (subset_univ _), Finset.card_pair hs.symm, card_univ]
  obtain ⟨Q, hQr, hQc⟩ := Finset.exists_subset_card_eq (s := rest) (n := n / 2 - 1)
    (by omega)
  let g : P → Fin 4 := fun x => if x = src then 0 else if x = s then 3 else if x ∈ Q then 1 else 2
  have hQ' : ∀ x ∈ Q, x ≠ src ∧ x ≠ s := fun x hx => by
    have := hQr hx; simp [hrest] at this; tauto
  have g0 : ∀ x, g x = 0 ↔ x = src := fun x => by
    simp only [g]; split_ifs <;> simp_all
  have g3 : ∀ x, g x = 3 ↔ x = s := fun x => by
    simp only [g]; split_ifs <;> simp_all [Ne.symm hs]
  have g1 : ∀ x, g x = 1 ↔ x ∈ Q := fun x => by
    have a1 : src ∉ Q := fun h => (hQ' _ h).1 rfl
    have a2 : s ∉ Q := fun h => (hQ' _ h).2 rfl
    simp only [g]; split_ifs with h1 h2 h3 <;> simp_all
  have N0 : (univ.filter fun x => g x = 0).card = 1 := by
    rw [Finset.card_eq_one]; exact ⟨src, by ext x; simp [g0]⟩
  have N3 : (univ.filter fun x => g x = 3).card = 1 := by
    rw [Finset.card_eq_one]; exact ⟨s, by ext x; simp [g3]⟩
  have N1 : (univ.filter fun x => g x = 1).card = n / 2 - 1 := by
    rw [← hQc]; congr 1; ext x; simp [g1]
  have Nsum : ∑ c : Fin 4, (univ.filter fun x => g x = c).card = n := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := g) (t := univ) (fun _ _ => mem_univ _), card_univ]
  rw [Fin.sum_univ_four, N0, N3, N1] at Nsum
  have hcard : ∀ w, (Fw g w).card ≤ t := by
    intro w
    rw [card_Fw]
    fin_cases w <;> simp [Fin.sum_univ_four, faultyT, N0, N3, N1] <;> omega
  -- non-empty groups
  obtain ⟨q, hqQ⟩ : Q.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨r, hr⟩ : (rest \ Q).Nonempty := Finset.card_pos.1 (by
    rw [Finset.card_sdiff_of_subset hQr]; omega)
  have hr' : g r = 2 := by
    have hrr := (Finset.mem_sdiff.1 hr)
    have : r ≠ src ∧ r ≠ s := by have := hrr.1; simp [hrest] at this; tauto
    simp only [g, this.1, this.2, hrr.2, ↓reduceIte]
  exact not_solvesIC_of_groups g src ((g0 src).2 rfl) ((g1 q).2 hqQ) hr' ((g3 s).2 rfl) hcard k A

/-! ### At most one non-faulty process: the degenerate cases `n ≤ 3` -/

/-- An algorithm that outputs its own private value as its own entry and solves interactive
consistency for `t' ≥ n - 2` faults solves it for any number of faults: with `n - 1` or more faulty
processes there is at most one non-faulty process. -/
theorem solvesIC_of_own {A : Alg P V} (hown : ∀ p τ, A p τ p = rep (τ [])) {k t' : ℕ}
    (ht' : Fintype.card P ≤ t' + 2) (hA : SolvesIC wne k t' A) (t : ℕ) : SolvesIC wne k t A := by
  intro F σ hF hm hpriv
  by_cases hFt : F.card ≤ t'
  · exact hA F σ hFt hm hpriv
  have uniq : ∀ p q, p ∉ F → q ∉ F → p = q := by
    intro p q hp hq
    by_contra hpq
    have : F ⊆ univ \ {p, q} := fun x hx => by
      simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and]
      rintro (rfl | rfl) <;> contradiction
    have := Finset.card_le_card this
    rw [Finset.card_sdiff_of_subset (subset_univ _), Finset.card_pair hpq, card_univ] at this
    omega
  refine ⟨fun p q hp hq => ?_, fun p p' q hp hp' => by rw [uniq p p' hp hp']⟩
  obtain rfl := uniq p q hp hq
  rw [hown, view_of_le (by simp)]
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 (hpriv p hp)
  rw [ha]; rfl

lemma alg2_own (t : ℕ) (p : P) (τ : List P → Option V) : alg2 t p τ p = rep (τ []) :=
  psl_self _ _ _ _

/-- For `n ≤ 3`, Algorithm 2 with parameter `n - 2` (i.e. `n - 1` rounds, at least one) solves
interactive consistency under weak non-equivocation for **every** `t`. -/
theorem solvesIC_small (hn : Fintype.card P ≤ 3) (t : ℕ) :
    SolvesIC wne (Fintype.card P - 2 + 1) t (alg2 (P := P) (V := V) (Fintype.card P - 2)) := by
  rcases Nat.eq_zero_or_pos (Fintype.card P) with h0 | h0
  · have : IsEmpty P := Fintype.card_eq_zero_iff.1 h0
    intro F σ _ _ _
    exact ⟨fun p => isEmptyElim p, fun p => isEmptyElim p⟩
  exact solvesIC_of_own (alg2_own _) (by omega) (theorem_5_1 (by omega)) t

/-- **Theorem 6.1 is false for `n = 3, t = 2`**: interactive consistency is solvable. -/
theorem theorem_6_1_false_n3 : ICSolvable (P := Fin 3) (V := V) wne 2 :=
  ⟨_, _, solvesIC_small (by simp) 2⟩

/-- **Theorem 6.1 is false for `n = 2, t = 1`**: interactive consistency is solvable. -/
theorem theorem_6_1_false_n2 : ICSolvable (P := Fin 2) (V := V) wne 1 :=
  ⟨_, _, solvesIC_small (by simp) 1⟩

/-- **The exact threshold** (Theorems 5.1 and 6.1, corrected): under weak non-equivocation,
interactive consistency is solvable iff `n > 2t` or `n ≤ 3`. -/
theorem icSolvable_wne_iff [Nontrivial V] {t : ℕ} :
    ICSolvable (P := P) (V := V) wne t ↔ 2 * t < Fintype.card P ∨ Fintype.card P ≤ 3 := by
  constructor
  · rintro ⟨k, A, hA⟩
    by_contra hc
    push Not at hc
    exact theorem_6_1 (by omega) (by omega) k A hA
  · rintro (h | h)
    · exact ⟨_, _, theorem_5_1 h⟩
    · exact ⟨_, _, solvesIC_small h t⟩

end NonEquivocation
