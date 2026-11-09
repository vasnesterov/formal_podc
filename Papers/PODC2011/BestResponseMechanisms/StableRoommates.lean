/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Podc.Foundations.GameTheory.NeverBestResponse

/-!
# Stable roommates as a best-response game (Section 3.1 of [NSVZ])

Nisan, Schapira, Valiant, Zohar, *Best-Response Mechanisms*, ICS 2011 / PODC 2011.

Students `i : ι`; student `i` may propose to any *acceptable* partner `j` (`acc i j`, a symmetric
irreflexive relation; the paper's game has `acc = (· ≠ ·)`, the bipartite intern–hospital repair
has `acc i j ↔ side i ≠ side j`). `α i j > 0` is the rank of `j` for `i` (larger = better,
injective on acceptable partners). Student `i` proposing to `j` gets `α i j` iff no other student
proposing to `j` is ranked by `j` above `i`, and `0` otherwise.

## Main results

* `theorem_3_1`: in a cycle-free game (with strict total tie-breaking orders) there is an NBR
  elimination of length `≤ n` ending at a profile `s` that is a clear outcome, a pure Nash
  equilibrium, the outcome of every NBR elimination, and whose matching (mutual proposals) is
  stable. Corollaries: `nbrSolvable`, `elimParam_le`, `hasClearOutcome`.
* `cycleFree_of_correlated`, `theorem_3_1_correlated`: correlated markets.
* `cycleFree_of_bipartite`, `theorem_3_1_internHospital`: intern–hospital markets with a common
  hospital ranking, where interns propose only to hospitals and vice versa (bipartite repair).
* `internHospital_counterexample`: in the paper's game (`acc = (· ≠ ·)`), an intern–hospital
  market (three interns with cyclic preferences, one hospital) is *not* NBR-solvable for any
  irreflexive tie-breaking and has no stable matching. Engine: `not_nbrSolvable_of_isBR`.
* `exists_two_nash`: without tie-breaking the PNE is not unique (odd `n`).
* `mechanism_isBR`: the announcement rule of the mechanism of Theorem 3.2 is a tie-broken best
  response.

## Proof structure

A *schedule* `(t, s)` fixes every student `i` at time `t i` to strategy `s i`, either as a pair of
mutual favourites among the students not fixed before (`Paired`) or as a student with no
acceptable partner left (`Dead`, `s i` = its tie-breaking favourite). `solves_of_good`,
`clearWitness_of_good`, `isStable_of_good` analyse the elimination sequence `elimSeq t s` of a
good schedule; `exists_good` builds one (≤ `n` steps) using `exists_mutual_favourites`, the
"follow your favourite" argument of the paper.
-/

open Set Function Cslib.GameTheory Cslib.GameTheory.TieBreakGame

namespace Podc.BestResponseMechanisms.StableRoommates

variable {ι : Type*}

/-! ### The model -/

/-- The strategies of student `i`: its acceptable partners. -/
abbrev Strat (acc : ι → ι → Prop) (i : ι) := {j : ι // acc i j}

/-- The utility of student `i` in the stable-roommates game: `α i j` if `i` proposes to `j` and no
other student proposing to `j` is ranked higher by `j`; `0` otherwise. -/
def util [Fintype ι] [DecidableEq ι] (acc : ι → ι → Prop) (α : ι → ι → ℕ) (i : ι)
    (s : ∀ j, Strat acc j) : ℕ :=
  if ∀ k, k ≠ i → (s k).1 = (s i).1 → ¬ α (s i).1 i < α (s i).1 k then α i (s i).1 else 0

/-- The stable-roommates game with tie-breaking rule `prec`. -/
@[reducible] def game [Fintype ι] [DecidableEq ι] (acc : ι → ι → Prop) (α : ι → ι → ℕ)
    (prec : ∀ i, Strat acc i → Strat acc i → Prop) : TieBreakGame ι (Strat acc) ℕ where
  utility := util acc α
  prec := prec

/-- A ranking cycle `r 0, r 1, …, r (k-1)` (`k > 2`, distinct students, indices mod `k`): each
`r (i+1)` ranks `r (i+2)` higher than `r i`. The game is *cycle-free* if there is none. -/
def CycleFree (acc : ι → ι → Prop) (α : ι → ι → ℕ) : Prop :=
  ∀ (k : ℕ) (r : ℕ → ι), 2 < k → (∀ i, r (i + k) = r i) → InjOn r (Iio k) →
    ¬ ∀ i, acc (r i) (r (i + 1)) ∧ α (r (i + 1)) (r i) < α (r (i + 1)) (r (i + 2))

/-- A (partial) matching: `m i = some j` iff `m j = some i`, between acceptable partners. -/
def IsMatching (acc : ι → ι → Prop) (m : ι → Option ι) : Prop :=
  ∀ i j, m i = some j → acc i j ∧ m j = some i

/-- `i` prefers `j` to its match `o` (being unmatched is worst). -/
def Prefers (α : ι → ι → ℕ) (i j : ι) : Option ι → Prop
  | none => True
  | some k => α i k < α i j

/-- A stable matching: no acceptable pair, not matched together, prefer each other to their
matches. -/
def IsStable (acc : ι → ι → Prop) (α : ι → ι → ℕ) (m : ι → Option ι) : Prop :=
  IsMatching acc m ∧ ∀ i j, acc i j → m i ≠ some j → ¬ (Prefers α i j (m i) ∧ Prefers α j i (m j))

/-- The matching induced by a profile: mutual proposals. -/
def matchingOf [DecidableEq ι] {acc : ι → ι → Prop} (s : ∀ j, Strat acc j) (i : ι) : Option ι :=
  if (s (s i).1).1 = i then some (s i).1 else none

/-! ### Utility lemmas -/

section Util

variable [Fintype ι] [DecidableEq ι] {acc : ι → ι → Prop} {α : ι → ι → ℕ}

lemma util_le (i : ι) (v : ∀ j, Strat acc j) : util acc α i v ≤ α i (v i).1 := by
  unfold util; split_ifs <;> omega

lemma util_eq_zero {i : ι} {v : ∀ j, Strat acc j} (p : ι) (hpi : p ≠ i)
    (hp : (v p).1 = (v i).1) (hlt : α (v i).1 i < α (v i).1 p) : util acc α i v = 0 := by
  unfold util
  split_ifs with h
  · exact absurd hlt (h p hpi hp)
  · rfl

lemma util_eq {i : ι} {v : ∀ j, Strat acc j}
    (h : ∀ p, p ≠ i → (v p).1 = (v i).1 → ¬ α (v i).1 i < α (v i).1 p) :
    util acc α i v = α i (v i).1 := by
  unfold util
  split_ifs
  rfl

end Util

/-! ### Fixing schedules

A schedule assigns to every student `i` a fixing time `t i` and a final strategy `s i`. At time
`t i`, student `i` is either *paired* (it and `(s i).1` are mutual favourites among the students
not fixed before) or *dead* (every acceptable partner was fixed before; `s i` is its tie-breaking
favourite). The elimination sequence `elimSeq t s` removes, at step `k`, all strategies but `s i`
of the students with `t i = k`. -/

section Schedule

variable [Fintype ι] [DecidableEq ι] {acc : ι → ι → Prop} {α : ι → ι → ℕ}
  (prec : ∀ i, Strat acc i → Strat acc i → Prop)

/-- `i` is paired with `(s i).1` at time `t i`: they propose to each other, are fixed at the same
time, and `(s i).1` is `i`'s favourite among the acceptable students not fixed before `t i`. -/
def Paired (t : ι → ℕ) (s : ∀ j, Strat acc j) (i : ι) : Prop :=
  (s (s i).1).1 = i ∧ t (s i).1 = t i ∧
    ∀ j, acc i j → t i ≤ t j → j ≠ (s i).1 → α i j < α i (s i).1

/-- `i` is dead at time `t i`: all its acceptable partners were fixed before, and `s i` is its
tie-breaking favourite. -/
def Dead (t : ι → ℕ) (s : ∀ j, Strat acc j) (i : ι) : Prop :=
  (∀ j, acc i j → t j < t i) ∧ ∀ y : Strat acc i, y ≠ s i → prec i y (s i)

/-- All students fixed before time `K` are paired or dead. -/
def Good (K : ℕ) (t : ι → ℕ) (s : ∀ j, Strat acc j) : Prop :=
  ∀ i, t i < K → Paired (α := α) t s i ∨ Dead prec t s i

/-- The elimination sequence of a schedule. -/
def elimSeq (t : ι → ℕ) (s : ∀ j, Strat acc j) : ℕ → Subgame (Strat acc) :=
  fun k i => {x | t i < k → x = s i}

variable {prec}

/-- Proposing to a student fixed before you were gives `0`. -/
lemma util_zero_of_fixed (hsymm : ∀ ⦃i j⦄, acc i j → acc j i) {K : ℕ} {t : ι → ℕ} {s : ∀ j, Strat acc j}
    (hG : Good (α := α) prec K t s) {i : ι} {k : ℕ} {v : ∀ j, Strat acc j}
    (hv : ∀ j, j ≠ i → t j < k → v j = s j) (hy : t (v i).1 < k) (hk : k ≤ t i)
    (hyK : t (v i).1 < K) : util acc α i v = 0 := by
  rcases hG (v i).1 hyK with ⟨hp1, hp2, hp3⟩ | ⟨hd1, -⟩
  · have hne : (s (v i).1).1 ≠ i := by
      intro h; rw [h] at hp2; omega
    apply util_eq_zero (s (v i).1).1 hne
    · rw [hv _ hne (by omega)]; exact hp1
    · exact hp3 i (hsymm (v i).2) (by omega) (Ne.symm hne)
  · exact absurd (hd1 i (hsymm (v i).2)) (by omega)

/-- A paired student proposing to its partner gets its partner's rank, whatever the students not
fixed before do. -/
lemma util_eq_of_paired (hsymm : ∀ ⦃i j⦄, acc i j → acc j i) {K : ℕ} {t : ι → ℕ} {s : ∀ j, Strat acc j}
    (hG : Good (α := α) prec K t s) {i : ι} (hiK : t i < K) (hpi : Paired (α := α) t s i)
    {v : ∀ j, Strat acc j} (hv : ∀ j, j ≠ i → t j < t i → v j = s j) (hvi : v i = s i) :
    util acc α i v = α i (s i).1 := by
  rw [util_eq, hvi]
  intro p hp hpv
  rw [hvi] at hpv ⊢
  obtain ⟨hi1, hi2, -⟩ := hpi
  rcases hG (s i).1 (by omega) with ⟨-, -, hg3⟩ | ⟨hd1, -⟩
  · rcases lt_or_ge (t p) (t i) with hlt | hge
    · rw [hv p hp hlt] at hpv
      rcases hG p (by omega) with ⟨-, hq2, -⟩ | ⟨hq1, -⟩
      · rw [hpv] at hq2; omega
      · have := hq1 _ (hpv ▸ (s p).2); omega
    · have := hg3 p (hsymm (hpv ▸ (v p).2)) (by omega) (by rw [hi1]; exact hp)
      rw [hi1] at this
      omega
  · have := hd1 i (hsymm (s i).2); omega

/-- The fixed strategy of a paired or dead student beats every other strategy against every
profile in which the students fixed earlier play their fixed strategies. -/
lemma beats_of_good (hsymm : ∀ ⦃i j⦄, acc i j → acc j i) (hpos : ∀ i j, acc i j → 0 < α i j)
    {K : ℕ} {t : ι → ℕ} {s : ∀ j, Strat acc j} (hG : Good (α := α) prec K t s)
    (htK : ∀ i, t i < K) {i : ι} {y : Strat acc i} (hy : y ≠ s i) {v : ∀ j, Strat acc j}
    (hv : ∀ j, j ≠ i → t j < t i → v j = s j) :
    (game acc α prec).Beats i (s i) y v := by
  have hv' : ∀ x : Strat acc i, ∀ j, j ≠ i → t j < t i → update v i x j = s j := by
    intro x j hj hjt
    rw [update_of_ne hj]; exact hv j hj hjt
  rcases hG i (htK i) with hp | hd
  · left
    change util acc α i _ < util acc α i _
    rw [util_eq_of_paired hsymm hG (htK i) hp (hv' _) (update_self _ _ _)]
    rcases lt_or_ge (t y.1) (t i) with hlt | hge
    · rw [util_zero_of_fixed hsymm hG (hv' y) (by rw [update_self]; exact hlt) le_rfl
        (by rw [update_self]; exact htK _)]
      exact hpos _ _ (s i).2
    · refine lt_of_le_of_lt (util_le _ _) ?_
      rw [update_self]
      exact hp.2.2 y.1 y.2 hge (fun h => hy (Subtype.ext h))
  · right
    change util acc α i _ = util acc α i _ ∧ prec i y (s i)
    refine ⟨?_, hd.2 y hy⟩
    rw [util_zero_of_fixed hsymm hG (hv' y) (by rw [update_self]; exact hd.1 _ y.2) le_rfl
        (by rw [update_self]; exact htK _),
      util_zero_of_fixed hsymm hG (hv' (s i)) (by rw [update_self]; exact hd.1 _ (s i).2) le_rfl
        (by rw [update_self]; exact htK _)]

omit [Fintype ι] [DecidableEq ι] in
lemma mem_elimSeq {t : ι → ℕ} {s : ∀ j, Strat acc j} {k : ℕ} {i : ι} {x : Strat acc i} :
    x ∈ elimSeq t s k i ↔ (t i < k → x = s i) := Iff.rfl

/-- A good schedule with all fixing times `< r` yields an NBR elimination of length `r` ending at
`s`. -/
theorem solves_of_good (hsymm : ∀ ⦃i j⦄, acc i j → acc j i) (hpos : ∀ i j, acc i j → 0 < α i j)
    {r : ℕ} {t : ι → ℕ} {s : ∀ j, Strat acc j} (hG : Good (α := α) prec r t s)
    (htr : ∀ i, t i < r) : (game acc α prec).Solves (elimSeq t s) r s := by
  refine ⟨⟨?_, fun k _ => ⟨fun i x hx h => hx (by omega), ?_⟩⟩, ?_⟩
  · funext i; ext x; simp [elimSeq, full]
  · intro i y hy hy'
    simp only [mem_elimSeq, not_imp] at hy hy'
    have hti : t i = k := by
      by_contra hne
      exact hy'.2 (hy (by omega))
    intro v hv
    refine ⟨s i, fun h => by omega, beats_of_good hsymm hpos hG htr hy'.2 ?_⟩
    intro j hj hjt
    exact hv j hj (by omega)
  · funext i; ext x
    simp only [mem_elimSeq, mem_singleton_iff]
    exact ⟨fun h => h (htr i), fun h _ => h⟩

/-- At its fixing time, every student gets in `s` the maximum utility of the current subgame. -/
theorem clearWitness_of_good (hsymm : ∀ ⦃i j⦄, acc i j → acc j i)
    (hpos : ∀ i j, acc i j → 0 < α i j)
    {r : ℕ} {t : ι → ℕ} {s : ∀ j, Strat acc j} (hG : Good (α := α) prec r t s)
    (htr : ∀ i, t i < r) (i : ι) :
    (game acc α prec).ClearWitness s i (elimSeq t s) r (t i) := by
  refine ⟨solves_of_good hsymm hpos hG htr, (htr i).le, ?_, ?_⟩
  · ext x; simp [mem_elimSeq]
  · intro v hv
    have hv' : ∀ j, j ≠ i → t j < t i → v j = s j := fun j _ h => hv j h
    change util acc α i v ≤ util acc α i s
    rcases hG i (htr i) with hp | hd
    · rw [util_eq_of_paired hsymm hG (htr i) hp (fun _ _ _ => rfl) rfl]
      rcases lt_or_ge (t (v i).1) (t i) with hlt | hge
      · rw [util_zero_of_fixed hsymm hG hv' hlt le_rfl (htr _)]; exact Nat.zero_le _
      · refine (util_le _ _).trans ?_
        by_cases he : (v i).1 = (s i).1
        · rw [he]
        · exact (hp.2.2 _ (v i).2 hge he).le
    · rw [util_zero_of_fixed hsymm hG hv' (hd.1 _ (v i).2) le_rfl (htr _)]
      exact Nat.zero_le _

omit [Fintype ι] in
lemma isMatching_matchingOf (s : ∀ j, Strat acc j) : IsMatching acc (matchingOf s) := by
  intro i j h
  unfold matchingOf at h ⊢
  split_ifs at h with h1
  cases h
  refine ⟨(s i).2, ?_⟩
  rw [ite_eq_left (by rw [h1])]
  rw [h1]

omit [Fintype ι] in
/-- The matching of a good schedule's profile is stable. -/
theorem isStable_of_good (hsymm : ∀ ⦃i j⦄, acc i j → acc j i) {r : ℕ} {t : ι → ℕ} {s : ∀ j, Strat acc j}
    (hG : Good (α := α) prec r t s) (htr : ∀ i, t i < r) : IsStable acc α (matchingOf s) := by
  refine ⟨isMatching_matchingOf s, ?_⟩
  · -- the student fixed first is not part of a blocking pair
    have key : ∀ i j, acc i j → t i ≤ t j → matchingOf s i ≠ some j →
        ¬ Prefers α i j (matchingOf s i) := by
      intro i j hij hle hm hpr
      rcases hG i (htr i) with ⟨hp1, -, hp3⟩ | ⟨hd1, -⟩
      · unfold matchingOf at hm hpr
        rw [ite_eq_left hp1] at hm hpr
        have hne : j ≠ (s i).1 := fun h => hm (by rw [h])
        exact absurd (hp3 j hij hle hne) (not_lt.2 (le_of_lt hpr))
      · have := hd1 j hij; omega
    intro i j hij hm ⟨h1, h2⟩
    rcases le_total (t i) (t j) with hle | hle
    · exact key i j hij hle hm h1
    · refine key j i (hsymm hij) hle (fun h => hm ((isMatching_matchingOf s j i h).2)) h2

end Schedule

/-! ### Construction of a good schedule -/

section Construction

variable {acc : ι → ι → Prop} {α : ι → ι → ℕ}

/-- In a cycle-free game, if every student of a nonempty finite set `U` has an acceptable partner
in `U`, then two students of `U` are mutual favourites within `U` (the "follow your favourite"
argument of the proof of Theorem 3.1). -/
theorem exists_mutual_favourites [Finite ι] (hsymm : ∀ ⦃i j⦄, acc i j → acc j i)
    (hirr : ∀ i, ¬ acc i i) (hinj : ∀ i j k, acc i j → acc i k → α i j = α i k → j = k)
    (hcf : CycleFree acc α) (U : Set ι) (hU : ∀ i ∈ U, ∃ j ∈ U, acc i j) {x : ι} (hx : x ∈ U) :
    ∃ a ∈ U, ∃ b ∈ U, acc a b ∧ (∀ j ∈ U, acc a j → j ≠ b → α a j < α a b) ∧
      (∀ j ∈ U, acc b j → j ≠ a → α b j < α b a) := by
  have hfav : ∀ i, ∃ j, i ∈ U →
      j ∈ U ∧ acc i j ∧ ∀ j' ∈ U, acc i j' → j' ≠ j → α i j' < α i j := by
    intro i
    by_cases hi : i ∈ U
    · obtain ⟨j, hj, hmax⟩ := Set.exists_max_image {j | j ∈ U ∧ acc i j} (α i)
        (Set.toFinite _) (by obtain ⟨j, hjU, hj⟩ := hU i hi; exact ⟨j, hjU, hj⟩)
      exact ⟨j, fun _ => ⟨hj.1, hj.2, fun j' hj'U hj' hne =>
        lt_of_le_of_ne (hmax j' ⟨hj'U, hj'⟩) (fun h => hne (hinj _ _ _ hj' hj.2 h))⟩⟩
    · exact ⟨i, fun h => absurd h hi⟩
  choose f hf using hfav
  have hfU : ∀ i ∈ U, f i ∈ U := fun i hi => (hf i hi).1
  have horb : ∀ n, f^[n] x ∈ U := by
    intro n
    induction n with
    | zero => exact hx
    | succ n ih => rw [iterate_succ_apply']; exact hfU _ ih
  obtain ⟨m, m', hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] x)
  have : ∃ m d, 0 < d ∧ f^[d] (f^[m] x) = f^[m] x := by
    rcases lt_or_gt_of_ne hne with h | h
    · exact ⟨m, m' - m, by omega, by
        rw [← iterate_add_apply, Nat.sub_add_cancel h.le]; exact heq.symm⟩
    · exact ⟨m', m - m', by omega, by
        rw [← iterate_add_apply, Nat.sub_add_cancel h.le]; exact heq⟩
  obtain ⟨m, d, hd, hper⟩ := this
  have hrU : ∀ n, f^[n] (f^[m] x) ∈ U := by intro n; rw [← iterate_add_apply]; exact horb _
  generalize f^[m] x = y at hper hrU
  have hyU : y ∈ U := hrU 0
  have hyper : IsPeriodicPt f d y := hper
  have hp := hyper.minimalPeriod_pos hd
  have hpp : IsPeriodicPt f (minimalPeriod f y) y := isPeriodicPt_minimalPeriod f y
  have hmem : y ∈ periodicPts f := mk_mem_periodicPts hp hpp
  rcases (show minimalPeriod f y = 1 ∨ minimalPeriod f y = 2 ∨ 2 < minimalPeriod f y by omega)
    with h1 | h2 | h3
  · exfalso
    rw [h1] at hpp
    have := (hf y hyU).2.1
    rw [show f y = y from hpp] at this
    exact hirr _ this
  · refine ⟨y, hyU, f y, hfU y hyU, (hf y hyU).2.1, (hf y hyU).2.2, ?_⟩
    have hffy : f (f y) = y := by rw [h2] at hpp; exact hpp
    have hb := hf (f y) (hfU y hyU)
    rw [hffy] at hb
    exact hb.2.2
  · exfalso
    refine hcf (minimalPeriod f y) (fun n => f^[n] y) h3 (fun n => ?_)
      iterate_injOn_Iio_minimalPeriod (fun n => ?_)
    · rw [iterate_add_apply, hpp]
    have hn := hf _ (hrU n)
    have hn1 := hf _ (hrU (n + 1))
    have hs1 : f^[n + 1] y = f (f^[n] y) := iterate_succ_apply' f n y
    have hs2 : f^[n + 2] y = f (f^[n + 1] y) := iterate_succ_apply' f (n + 1) y
    refine ⟨by rw [hs1]; exact hn.2.1, ?_⟩
    rw [hs2]
    refine hn1.2.2 _ (hrU n) (hsymm (by rw [hs1]; exact hn.2.1)) ?_
    intro heq2
    have hz : IsPeriodicPt f 2 (f^[n] y) := by
      change f^[2] (f^[n] y) = f^[n] y
      rw [← iterate_add_apply, add_comm, hs2]
      exact heq2.symm
    have := hz.minimalPeriod_le (by norm_num)
    rw [minimalPeriod_apply_iterate hmem] at this
    omega

/-- A strict total order on a finite nonempty type has a maximum. -/
-- CSLib candidate
lemma exists_max_of_isStrictTotalOrder {β : Type*} [Finite β] [Nonempty β] (r : β → β → Prop)
    [IsStrictTotalOrder β r] : ∃ m, ∀ y, y ≠ m → r y m := by
  let r' : β → β → Prop := fun a b => r b a
  have : IsTrans β r' := ⟨fun a b c hab hbc => (_root_.trans (hbc : r c b) (hab : r b a) : r c a)⟩
  have : Std.Irrefl r' := ⟨fun a => irrefl (r := r) a⟩
  have hwf : WellFounded r' := Finite.wellFounded_of_trans_of_irrefl r'
  obtain ⟨m, -, hm⟩ := hwf.has_min univ ⟨Classical.arbitrary β, trivial⟩
  refine ⟨m, fun y hy => ?_⟩
  rcases trichotomous_of r y m with h | h | h
  · exact h
  · exact absurd h hy
  · exact absurd h (hm y trivial)

end Construction

section Step

variable [Fintype ι] [DecidableEq ι] {acc : ι → ι → Prop} {α : ι → ι → ℕ}
  {prec : ∀ i, Strat acc i → Strat acc i → Prop}

/-- The fixing times after step `K`: students with `N i` (not fixed before) get time `K`, the
remaining unfixed students get `K + 1`. -/
def bump (t : ι → ℕ) (K : ℕ) (N : ι → Prop) [DecidablePred N] (i : ι) : ℕ :=
  if t i < K then t i else if N i then K else K + 1

omit [Fintype ι] [DecidableEq ι] in
lemma good_bump {K : ℕ} {t : ι → ℕ} {s s' : ∀ j, Strat acc j} (N : ι → Prop) [DecidablePred N]
    (hG : Good (α := α) prec K t s) (hs : ∀ i, t i < K → s' i = s i)
    (hnew : ∀ i, K ≤ t i → N i →
      Paired (α := α) (bump t K N) s' i ∨ Dead prec (bump t K N) s' i) :
    Good (α := α) prec (K + 1) (bump t K N) s' := by
  have hlt : ∀ i, t i < K → bump t K N i = t i := fun i h => by simp [bump, h]
  have hge : ∀ i, K ≤ t i → K ≤ bump t K N i := fun i h => by
    unfold bump; split_ifs <;> omega
  intro i hi
  by_cases hiK : t i < K
  · have hti := hlt i hiK
    rcases hG i hiK with ⟨hp1, hp2, hp3⟩ | ⟨hd1, hd2⟩
    · left
      have hg : t (s i).1 < K := by omega
      refine ⟨?_, ?_, ?_⟩
      · rw [hs i hiK, hs _ hg]; exact hp1
      · rw [hs i hiK, hlt _ hg, hti, hp2]
      · intro j hij hle hne
        rw [hs i hiK] at hne ⊢
        refine hp3 j hij ?_ hne
        by_cases hj : t j < K
        · rw [hti, hlt j hj] at hle; exact hle
        · omega
    · right
      refine ⟨fun j hij => ?_, ?_⟩
      · have := hd1 j hij
        rw [hti, hlt j (by omega)]; exact this
      · rw [hs i hiK]; exact hd2
  · have hN : N i := by
      by_contra hN
      simp [bump, hiK, hN] at hi
    exact hnew i (by omega) hN

omit [Fintype ι] [DecidableEq ι] in
lemma bump_ge' {K : ℕ} {t : ι → ℕ} {N : ι → Prop} [DecidablePred N] {i : ι}
    (h : K ≤ bump t K N i) : K ≤ t i := by
  unfold bump at h; split_ifs at h <;> omega

omit [Fintype ι] [DecidableEq ι] in
lemma bump_of_new {K : ℕ} {t : ι → ℕ} {N : ι → Prop} [DecidablePred N] {i : ι}
    (hi : K ≤ t i) (hN : N i) : bump t K N i = K := by
  simp [bump, hN, not_lt.2 hi]

omit [Fintype ι] [DecidableEq ι] in
lemma bump_ge {K : ℕ} {t : ι → ℕ} {N : ι → Prop} [DecidablePred N] {i : ι}
    (h : K + 1 ≤ bump t K N i) : K ≤ t i := by
  unfold bump at h; split_ifs at h <;> omega

omit [DecidableEq ι] in
lemma card_bump_lt {K : ℕ} {t : ι → ℕ} {N : ι → Prop} [DecidablePred N] {i : ι}
    (hi : K ≤ t i) (hN : N i) :
    (Finset.univ.filter (fun j => K + 1 ≤ bump t K N j)).card <
      (Finset.univ.filter (fun j => K ≤ t j)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨i, by simp [hi], ?_⟩
    simp [bump, hN, not_lt.2 hi]
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact bump_ge hj

/-- One step of the construction: fix a dead student or a pair of mutual favourites. -/
lemma exists_good_step (hsymm : ∀ ⦃i j⦄, acc i j → acc j i) (hirr : ∀ i, ¬ acc i i)
    (hinj : ∀ i j k, acc i j → acc i k → α i j = α i k → j = k) (hcf : CycleFree acc α)
    [∀ i, IsStrictTotalOrder (Strat acc i) (prec i)] (hne : ∀ i, Nonempty (Strat acc i))
    {K : ℕ} {t : ι → ℕ} {s : ∀ j, Strat acc j} (hG : Good (α := α) prec K t s)
    {x : ι} (hx : K ≤ t x) :
    ∃ t' s', Good (α := α) prec (K + 1) t' s' ∧
      (Finset.univ.filter (fun j => K + 1 ≤ t' j)).card <
        (Finset.univ.filter (fun j => K ≤ t j)).card := by
  by_cases hdead : ∃ d, K ≤ t d ∧ ∀ j, K ≤ t j → ¬ acc d j
  · obtain ⟨d, hd, hdj⟩ := hdead
    have := hne d
    obtain ⟨m, hm⟩ := exists_max_of_isStrictTotalOrder (prec d)
    refine ⟨bump t K (· = d), update s d m, good_bump _ hG (fun i hi => ?_) ?_,
      card_bump_lt hd rfl⟩
    · exact update_of_ne (by rintro rfl; omega) _ _
    · rintro i - rfl
      right
      refine ⟨fun j hj => ?_, ?_⟩
      · rw [bump_of_new (N := fun x => x = i) hd rfl]
        have : t j < K := by
          by_contra h; exact hdj j (by omega) hj
        simp [bump, this]
      · rw [update_self]; exact hm
  · push Not at hdead
    obtain ⟨a, haU, b, hbU, hab, ha, hb⟩ := exists_mutual_favourites hsymm hirr hinj hcf
      {j | K ≤ t j} (fun i hi => hdead i hi) (x := x) hx
    have hne' : a ≠ b := by rintro rfl; exact hirr _ hab
    let s' := update (update s a ⟨b, hab⟩) b ⟨a, hsymm hab⟩
    have hsa : s' a = ⟨b, hab⟩ := by
      simp only [s']; rw [update_of_ne hne', update_self]
    have hsb : s' b = ⟨a, hsymm hab⟩ := by simp only [s', update_self]
    refine ⟨bump t K (fun i => i = a ∨ i = b), s', good_bump _ hG (fun i hi => ?_) ?_,
      card_bump_lt (N := fun i => i = a ∨ i = b) haU (Or.inl rfl)⟩
    · simp only [s']
      have h1 : i ≠ a := by rintro rfl; exact absurd haU (not_le.2 hi)
      have h2 : i ≠ b := by rintro rfl; exact absurd hbU (not_le.2 hi)
      rw [update_of_ne h2, update_of_ne h1]
    · rintro i - (rfl | rfl)
      · left
        refine ⟨by rw [hsa, hsb], by rw [hsa, bump_of_new hbU (Or.inr rfl),
          bump_of_new haU (Or.inl rfl)], fun j hj hle hjne => ?_⟩
        rw [hsa] at hjne ⊢
        rw [bump_of_new haU (Or.inl rfl)] at hle
        exact ha j (bump_ge' hle) hj hjne
      · left
        refine ⟨by rw [hsb, hsa], by rw [hsb, bump_of_new haU (Or.inl rfl),
          bump_of_new hbU (Or.inr rfl)], fun j hj hle hjne => ?_⟩
        rw [hsb] at hjne ⊢
        rw [bump_of_new hbU (Or.inr rfl)] at hle
        exact hb j (bump_ge' hle) hj hjne

/-- A cycle-free game has a good schedule with at most `n` steps. -/
theorem exists_good (hsymm : ∀ ⦃i j⦄, acc i j → acc j i) (hirr : ∀ i, ¬ acc i i)
    (hinj : ∀ i j k, acc i j → acc i k → α i j = α i k → j = k) (hcf : CycleFree acc α)
    [∀ i, IsStrictTotalOrder (Strat acc i) (prec i)] (hne : ∀ i, Nonempty (Strat acc i)) :
    ∃ r t s, Good (α := α) prec r t s ∧ (∀ i, t i < r) ∧ r ≤ Fintype.card ι := by
  suffices h : ∀ c K t s, Good (α := α) prec K t s →
      (Finset.univ.filter (fun j => K ≤ t j)).card ≤ c →
      ∃ r t' s', Good (α := α) prec r t' s' ∧ (∀ i, t' i < r) ∧ r ≤ K + c by
    obtain ⟨r, t, s, h1, h2, h3⟩ := h _ 0 (fun _ => 0) (fun i => Classical.choice (hne i))
      (fun i h => absurd h (Nat.not_lt_zero _)) (Finset.card_le_univ _)
    exact ⟨r, t, s, h1, h2, by omega⟩
  intro c
  induction c with
  | zero =>
    intro K t s hG hc
    refine ⟨K, t, s, hG, fun i => ?_, by omega⟩
    by_contra h
    rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hc
    exact hc (Finset.mem_univ i) (by omega)
  | succ c ih =>
    intro K t s hG hc
    by_cases hU : ∃ i, K ≤ t i
    · obtain ⟨x, hx⟩ := hU
      obtain ⟨t', s', hG', hlt⟩ := exists_good_step hsymm hirr hinj hcf hne hG hx
      obtain ⟨r, t'', s'', h1, h2, h3⟩ := ih (K + 1) t' s' hG' (by omega)
      exact ⟨r, t'', s'', h1, h2, by omega⟩
    · push Not at hU
      exact ⟨K, t, s, hG, hU, by omega⟩

end Step

/-! ### Theorem 3.1 -/

section Main

variable [Fintype ι] [DecidableEq ι] {acc : ι → ι → Prop} {α : ι → ι → ℕ}

/-- **Theorem 3.1 of [NSVZ]** (for cycle-free stable-roommates games, generalised to a symmetric
irreflexive acceptability relation `acc`). With strict total tie-breaking orders, there is an NBR
elimination `E 0, …, E r` with `r ≤ n` ending at a profile `s` such that

* `s` is a clear outcome (for every student `i`, at the step `k` where `i`'s strategies start
  being eliminated, `s` gives `i` the maximum utility in `E k`),
* `s` is a pure Nash equilibrium and the outcome of every NBR elimination,
* the matching of mutual proposals of `s` is stable. -/
theorem theorem_3_1 (hsymm : ∀ ⦃i j⦄, acc i j → acc j i) (hirr : ∀ i, ¬ acc i i)
    (hpos : ∀ i j, acc i j → 0 < α i j)
    (hinj : ∀ i j k, acc i j → acc i k → α i j = α i k → j = k) (hcf : CycleFree acc α)
    (prec : ∀ i, Strat acc i → Strat acc i → Prop)
    [∀ i, IsStrictTotalOrder (Strat acc i) (prec i)] (hne : ∀ i, Nonempty (Strat acc i)) :
    ∃ (E : ℕ → Subgame (Strat acc)) (r : ℕ) (s : ∀ i, Strat acc i),
      (game acc α prec).Solves E r s ∧ r ≤ Fintype.card ι ∧
      (∀ i, ∃ k ≤ r, (game acc α prec).ClearWitness s i E r k) ∧
      (game acc α prec).IsNash s ∧
      (∀ E' r' s', (game acc α prec).Solves E' r' s' → s' = s) ∧
      IsStable acc α (matchingOf s) := by
  obtain ⟨r, t, s, hG, htr, hr⟩ := exists_good (α := α) (prec := prec) hsymm hirr hinj hcf hne
  have hS := solves_of_good hsymm hpos hG htr
  have hBR : (game acc α prec).HasBR := hasBR_of_finite
  exact ⟨elimSeq t s, r, s, hS, hr,
    fun i => ⟨t i, (htr i).le, clearWitness_of_good hsymm hpos hG htr i⟩,
    hS.isNash hBR, fun _ _ _ h' => h'.unique hBR hS |>.symm ▸ rfl,
    isStable_of_good hsymm hG htr⟩

/-- Theorem 3.1, first bullet: cycle-free games are NBR-solvable (under tie-breaking). -/
theorem nbrSolvable (hsymm : ∀ ⦃i j⦄, acc i j → acc j i) (hirr : ∀ i, ¬ acc i i)
    (hpos : ∀ i j, acc i j → 0 < α i j)
    (hinj : ∀ i j k, acc i j → acc i k → α i j = α i k → j = k) (hcf : CycleFree acc α)
    (prec : ∀ i, Strat acc i → Strat acc i → Prop)
    [∀ i, IsStrictTotalOrder (Strat acc i) (prec i)] (hne : ∀ i, Nonempty (Strat acc i)) :
    (game acc α prec).NBRSolvable := by
  obtain ⟨E, r, s, hS, -⟩ := theorem_3_1 hsymm hirr hpos hinj hcf prec hne
  exact ⟨E, r, s, hS⟩

/-- Theorem 3.1, third bullet: `e_G ≤ n`. -/
theorem elimParam_le (hsymm : ∀ ⦃i j⦄, acc i j → acc j i) (hirr : ∀ i, ¬ acc i i)
    (hpos : ∀ i j, acc i j → 0 < α i j)
    (hinj : ∀ i j k, acc i j → acc i k → α i j = α i k → j = k) (hcf : CycleFree acc α)
    (prec : ∀ i, Strat acc i → Strat acc i → Prop)
    [∀ i, IsStrictTotalOrder (Strat acc i) (prec i)] (hne : ∀ i, Nonempty (Strat acc i)) :
    (game acc α prec).elimParam ≤ Fintype.card ι := by
  obtain ⟨E, r, s, hS, hr, -⟩ := theorem_3_1 hsymm hirr hpos hinj hcf prec hne
  exact (Nat.sInf_le (show r ∈ {r | ∃ E s, (game acc α prec).Solves E r s} from ⟨E, s, hS⟩)).trans hr

/-- Theorem 3.1 with Definition 2.6: the outcome is a clear outcome, and its matching is stable. -/
theorem hasClearOutcome (hsymm : ∀ ⦃i j⦄, acc i j → acc j i) (hirr : ∀ i, ¬ acc i i)
    (hpos : ∀ i j, acc i j → 0 < α i j)
    (hinj : ∀ i j k, acc i j → acc i k → α i j = α i k → j = k) (hcf : CycleFree acc α)
    (prec : ∀ i, Strat acc i → Strat acc i → Prop)
    [∀ i, IsStrictTotalOrder (Strat acc i) (prec i)] (hne : ∀ i, Nonempty (Strat acc i)) :
    ∃ s, (game acc α prec).HasClearOutcome s ∧ IsStable acc α (matchingOf s) := by
  obtain ⟨E, r, s, hS, -, hcw, -, -, hst⟩ := theorem_3_1 hsymm hirr hpos hinj hcf prec hne
  exact ⟨s, ⟨⟨E, r, hS⟩, fun i => by obtain ⟨k, -, hk⟩ := hcw i; exact ⟨E, r, k, hk⟩⟩, hst⟩

end Main

/-! ### Correlated and bipartite intern–hospital markets are cycle-free -/

section CycleFree

variable {acc : ι → ι → Prop} {α : ι → ι → ℕ}

/-- **Correlated markets are cycle-free** (proof of Theorem 3.1): if rankings are consistent with
symmetric edge weights `w` (a heavier edge means a higher rank), there is no ranking cycle. -/
theorem cycleFree_of_correlated {β : Type*} [LinearOrder β] (hsymm : ∀ ⦃i j⦄, acc i j → acc j i)
    (w : ι → ι → β) (hw : ∀ i j, w i j = w j i)
    (hα : ∀ i j k, acc i j → acc i k → α i j < α i k → w i j < w i k) : CycleFree acc α := by
  intro k r hk hper _ hcyc
  have hc : StrictMono (fun n => w (r n) (r (n + 1))) := by
    refine strictMono_nat_of_lt_succ (fun n => ?_)
    have := hα _ _ _ (hsymm (hcyc n).1) (hcyc (n + 1)).1 (hcyc n).2
    rw [hw] at this
    simpa [add_assoc] using this
  have h1 := hc (show 0 < k by omega)
  have e0 : r k = r 0 := by simpa using hper 0
  have e1 : r (k + 1) = r 1 := by rw [show k + 1 = 1 + k by omega]; exact hper 1
  simp only [e0, e1] at h1
  exact lt_irrefl _ h1

/-- **Bipartite intern–hospital markets with a common hospital ranking are cycle-free.** Students
are interns (`side i = false`) and hospitals (`side i = true`); acceptable partners are on the other
side; all hospitals rank the interns in the same order. -/
theorem cycleFree_of_bipartite (side : ι → Bool) (hacc : ∀ i j, acc i j ↔ side i ≠ side j)
    (hcommon : ∀ h h' i j, side h = true → side h' = true → side i = false → side j = false →
      α h i < α h j → α h' i < α h' j) : CycleFree acc α := by
  intro k r hk hper _ hcyc
  have halt : ∀ n, side (r (n + 1)) = !side (r n) := by
    intro n
    have := (hacc _ _).1 (hcyc n).1
    cases h : side (r n) <;> cases h' : side (r (n + 1)) <;> simp_all
  have h2 : ∀ n, side (r (n + 2)) = side (r n) := by
    intro n; rw [halt (n + 1), halt n, Bool.not_not]
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, side (r i₀) = false := by
    cases h : side (r 0)
    · exact ⟨0, h⟩
    · exact ⟨1, by rw [halt 0, h]; rfl⟩
  have hint : ∀ j, side (r (i₀ + 2 * j)) = false := by
    intro j
    induction j with
    | zero => exact hi₀
    | succ j ih => rw [show i₀ + 2 * (j + 1) = i₀ + 2 * j + 2 by ring, h2, ih]
  have hhosp : ∀ j, side (r (i₀ + 2 * j + 1)) = true := by
    intro j; rw [halt, hint]; rfl
  have hd : StrictMono (fun j => α (r (i₀ + 1)) (r (i₀ + 2 * j))) := by
    refine strictMono_nat_of_lt_succ (fun j => ?_)
    have := (hcyc (i₀ + 2 * j)).2
    refine hcommon _ _ _ _ (hhosp j) (by simpa using hhosp 0) (hint j) (hint (j + 1)) ?_
    simpa [show i₀ + 2 * (j + 1) = i₀ + 2 * j + 1 + 1 by ring] using this
  have h1 := hd (show 0 < k by omega)
  simp only [mul_zero, add_zero, show i₀ + 2 * k = (i₀ + k) + k by ring, hper] at h1
  exact lt_irrefl _ h1

end CycleFree

/-! ### Theorem 3.1 for the two special cases -/

section SpecialCases

variable [Fintype ι] [DecidableEq ι] {α : ι → ι → ℕ}

/-- The conclusion of Theorem 3.1 (as in `theorem_3_1`): an NBR elimination of length `≤ n`
ending at a clear outcome `s` that is a pure Nash equilibrium, the outcome of every NBR
elimination, and induces a stable matching. -/
def Theorem31Conclusion (acc : ι → ι → Prop) (α : ι → ι → ℕ)
    (prec : ∀ i, Strat acc i → Strat acc i → Prop) : Prop :=
  ∃ (E : ℕ → Subgame (Strat acc)) (r : ℕ) (s : ∀ i, Strat acc i),
    (game acc α prec).Solves E r s ∧ r ≤ Fintype.card ι ∧
    (∀ i, ∃ k ≤ r, (game acc α prec).ClearWitness s i E r k) ∧
    (game acc α prec).IsNash s ∧
    (∀ E' r' s', (game acc α prec).Solves E' r' s' → s' = s) ∧
    IsStable acc α (matchingOf s)

/-- **Theorem 3.1 of [NSVZ], correlated markets.** Every student may propose to every other
student; ranks are strict, positive, and consistent with symmetric edge weights `w`. -/
theorem theorem_3_1_correlated [Nontrivial ι] {β : Type*} [LinearOrder β]
    (hpos : ∀ i j, i ≠ j → 0 < α i j) (hinj : ∀ i j k, i ≠ j → i ≠ k → α i j = α i k → j = k)
    (w : ι → ι → β) (hw : ∀ i j, w i j = w j i)
    (hα : ∀ i j k, i ≠ j → i ≠ k → α i j < α i k → w i j < w i k)
    (prec : ∀ i, Strat (· ≠ ·) i → Strat (· ≠ ·) i → Prop)
    [∀ i, IsStrictTotalOrder (Strat (· ≠ ·) i) (prec i)] :
    Theorem31Conclusion (· ≠ ·) α prec :=
  theorem_3_1 (fun _ _ h => Ne.symm h) (fun i h => h rfl) hpos hinj
    (cycleFree_of_correlated (fun _ _ h => Ne.symm h) w hw hα) prec
    (fun i => by obtain ⟨j, hj⟩ := exists_ne i; exact ⟨⟨j, Ne.symm hj⟩⟩)

/-- **Theorem 3.1 of [NSVZ], intern–hospital matchings (bipartite repair).** Interns
(`side i = false`) propose only to hospitals and hospitals only to interns; all hospitals rank the
interns in the same order; there is at least one intern and one hospital. -/
theorem theorem_3_1_internHospital (side : ι → Bool)
    (hpos : ∀ i j, side i ≠ side j → 0 < α i j)
    (hinj : ∀ i j k, side i ≠ side j → side i ≠ side k → α i j = α i k → j = k)
    (hcommon : ∀ h h' i j, side h = true → side h' = true → side i = false → side j = false →
      (α h i < α h j ↔ α h' i < α h' j))
    (hI : ∃ i, side i = false) (hH : ∃ h, side h = true)
    (prec : ∀ i, Strat (fun i j => side i ≠ side j) i → Strat (fun i j => side i ≠ side j) i → Prop)
    [∀ i, IsStrictTotalOrder (Strat (fun i j => side i ≠ side j) i) (prec i)] :
    Theorem31Conclusion (fun i j => side i ≠ side j) α prec := by
  refine theorem_3_1 (fun _ _ h => Ne.symm h) (fun i h => h rfl) hpos hinj
    (cycleFree_of_bipartite side (fun _ _ => Iff.rfl)
      (fun h h' i j a b c d => (hcommon h h' i j a b c d).1)) prec (fun i => ?_)
  obtain ⟨a, ha⟩ := hI
  obtain ⟨b, hb⟩ := hH
  cases h : side i
  · exact ⟨⟨b, show side i ≠ side b by rw [h, hb]; decide⟩⟩
  · exact ⟨⟨a, show side i ≠ side a by rw [h, ha]; decide⟩⟩

end SpecialCases

/-! ### Non-vacuity and the role of tie-breaking -/

section Examples

/-- Ranks on three students: `α i j = i + j + 1`, consistent with the weights `w i j = i + j`
(a correlated market). -/
def exα (i j : Fin 3) : ℕ := i.val + j.val + 1

instance exPrec_isStrictTotalOrder (i : Fin 3) :
    IsStrictTotalOrder (Strat (· ≠ ·) i) (fun x y => x.1 < y.1) :=
  inferInstanceAs (IsStrictTotalOrder {j : Fin 3 // i ≠ j} (· < ·))

/-- The hypotheses of the correlated case are satisfiable. -/
example : Theorem31Conclusion (· ≠ ·) exα (fun _ x y => x.1 < y.1) :=
  theorem_3_1_correlated (by decide) (by decide) (fun i j => i.val + j.val)
    (fun i j => Nat.add_comm _ _) (fun i j k _ _ h => by simpa [exα] using h) _

/-- Without tie-breaking, the PNE is not unique when `n` is odd: in the correlated market `exα`,
students `1, 2` are mutual favourites and student `0` gets `0` whatever it does; both profiles
`(0 → 1, 1 → 2, 2 → 1)` and `(0 → 2, 1 → 2, 2 → 1)` are pure Nash equilibria. -/
theorem exists_two_nash :
    ∃ s t : ∀ i : Fin 3, Strat (· ≠ ·) i, s ≠ t ∧
      (game (· ≠ ·) exα (fun _ x y => x.1 < y.1)).IsNash s ∧
      (game (· ≠ ·) exα (fun _ x y => x.1 < y.1)).IsNash t := by
  refine ⟨fun i => ⟨![1, 2, 1] i, by revert i; decide⟩,
    fun i => ⟨![2, 2, 1] i, by revert i; decide⟩, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun s => (s 0).1) h
    simp at this
  · unfold IsNash; decide
  · unfold IsNash; decide

end Examples

/-! ### The mechanism of Theorem 3.2 plays tie-broken best responses -/

section Mechanism

variable [Fintype ι] [DecidableEq ι] {acc : ι → ι → Prop} {α : ι → ι → ℕ}

/-- Student `i` can make a *better offer* to `j` (mechanism of Theorem 3.2): `j` prefers `i` to
every other student whose current announcement is `j`. -/
def BetterOffer (α : ι → ι → ℕ) (v : ∀ j, Strat acc j) (i j : ι) : Prop :=
  ∀ k, k ≠ i → (v k).1 = j → α j k < α j i

open Classical in
/-- The utility of announcing `y` is `α i y` if `i` can make a better offer to `y`, and `0`
otherwise. -/
lemma util_update_eq (hsymm : ∀ ⦃i j⦄, acc i j → acc j i)
    (hinj : ∀ i j k, acc i j → acc i k → α i j = α i k → j = k) (v : ∀ j, Strat acc j) (i : ι)
    (y : Strat acc i) :
    util acc α i (update v i y) = if BetterOffer α v i y.1 then α i y.1 else 0 := by
  split_ifs with hb
  · rw [util_eq, update_self]
    intro p hp hpy
    rw [update_of_ne hp, update_self] at hpy
    rw [update_self]
    exact not_lt.2 (hb p hp hpy).le
  · unfold BetterOffer at hb
    push Not at hb
    obtain ⟨k, hk, hky, hle⟩ := hb
    refine util_eq_zero k hk (by rw [update_of_ne hk, update_self, hky]) ?_
    rw [update_self]
    refine lt_of_le_of_ne hle (fun h => hk ?_)
    exact (hinj _ _ _ (hsymm y.2) (hsymm (hky ▸ (v k).2)) h).symm

/-- **Theorem 3.2 of [NSVZ], the mechanism's step.** Announcing the most preferred student to whom
one can make a better offer is a tie-broken best response (for any irreflexive tie-breaking). -/
theorem mechanism_isBR (hsymm : ∀ ⦃i j⦄, acc i j → acc j i)
    (hpos : ∀ i j, acc i j → 0 < α i j)
    (hinj : ∀ i j k, acc i j → acc i k → α i j = α i k → j = k)
    (prec : ∀ i, Strat acc i → Strat acc i → Prop) (hirr : ∀ i, Std.Irrefl (prec i))
    (v : ∀ j, Strat acc j) (i : ι) (x : Strat acc i) (hx : BetterOffer α v i x.1)
    (hmax : ∀ y : Strat acc i, BetterOffer α v i y.1 → α i y.1 ≤ α i x.1) :
    (game acc α prec).IsBR i x v := by
  intro y hy
  change util acc α i _ < util acc α i _ ∨ (util acc α i _ = util acc α i _ ∧ prec i x y) at hy
  by_cases hyx : y = x
  · subst hyx
    rcases hy with h | h
    · exact lt_irrefl _ h
    · exact (hirr i).irrefl _ h.2
  · rw [util_update_eq hsymm hinj, util_update_eq hsymm hinj, ite_eq_left hx] at hy
    have hne : α i y.1 ≠ α i x.1 :=
      fun h => hyx (Subtype.ext (hinj _ _ _ y.2 x.2 h))
    split_ifs at hy with hb
    · have := hmax y hb
      rcases hy with h | h <;> omega
    · have := hpos _ _ x.2
      rcases hy with h | h <;> omega

end Mechanism

/-! ### A general obstruction to NBR-solvability -/

section Obstruction

variable {ι : Type*} {S : ι → Type*} {R : Type*} [DecidableEq ι] [LinearOrder R]

-- CSLib candidate
/-- If every strategy of a product subgame `H` is a tie-broken best response to some profile of
`H`, then no NBR elimination ever removes a strategy of `H`. -/
theorem subset_elimSeq_of_isBR (G : TieBreakGame ι S R) (H : Subgame S)
    (hH : ∀ i, ∀ x ∈ H i, ∃ v : ∀ j, S j, (∀ j, j ≠ i → v j ∈ H j) ∧ G.IsBR i x v)
    {E : ℕ → Subgame S} {r : ℕ} (hE : G.IsElimSeq E r) :
    ∀ k ≤ r, ∀ i, H i ⊆ E k i := by
  intro k
  induction k with
  | zero => intro _ i x _; exact hE.zero i x
  | succ k ih =>
    intro hk i x hx
    obtain ⟨v, hv, hbr⟩ := hH i x hx
    exact hE.mem_of_isBR hbr (k := k) (by omega) (fun l hl => ih (by omega) l (hv l hl))
      le_rfl hk

-- CSLib candidate
/-- If every strategy of a product subgame `H` with two strategies for some player is a
tie-broken best response to some profile of `H`, the game is not NBR-solvable. -/
theorem not_nbrSolvable_of_isBR (G : TieBreakGame ι S R) (H : Subgame S)
    (hH : ∀ i, ∀ x ∈ H i, ∃ v : ∀ j, S j, (∀ j, j ≠ i → v j ∈ H j) ∧ G.IsBR i x v)
    {i : ι} {x y : S i} (hx : x ∈ H i) (hy : y ∈ H i) (hxy : x ≠ y) : ¬ G.NBRSolvable := by
  rintro ⟨E, r, s, hE, hEr⟩
  have h := subset_elimSeq_of_isBR G H hH hE r le_rfl i
  rw [hEr] at h
  exact hxy ((h hx).trans (h hy).symm)

end Obstruction

/-! ### The literal intern–hospital claim fails (counterexample) -/

section Counterexample

/-- The utility as a function of the plain proposal map. -/
def utilF (α : ι → ι → ℕ) [Fintype ι] [DecidableEq ι] (i : ι) (f : ι → ι) : ℕ :=
  if ∀ k, k ≠ i → f k = f i → ¬ α (f i) i < α (f i) k then α i (f i) else 0

lemma util_eq_utilF [Fintype ι] [DecidableEq ι] {acc : ι → ι → Prop} (α : ι → ι → ℕ) (i : ι)
    (s : ∀ j, Strat acc j) : util acc α i s = utilF α i (fun j => (s j).1) := rfl

lemma val_update [DecidableEq ι] {acc : ι → ι → Prop} (v : ∀ j, Strat acc j) (i : ι)
    (y : Strat acc i) : (fun j => (update v i y j).1) = update (fun j => (v j).1) i y.1 := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

/-- Ranks (`cxα i j`, larger = better). Students `0, 1, 2` are interns with the cyclic preferences
`0 : 1 > 2 > 3`, `1 : 2 > 0 > 3`, `2 : 0 > 1 > 3`; student `3` is the only hospital,
ranking `0 > 1 > 2`. Every student ranks the hospital last. -/
def cxα : Fin 4 → Fin 4 → ℕ :=
  ![![0, 3, 2, 1], ![2, 0, 3, 1], ![3, 2, 0, 1], ![3, 2, 1, 0]]

/-- The ranking cycle `0, 1, 2, 0, 1, 2, …` of the counterexample. -/
def cxCyc (n : ℕ) : Fin 4 := ⟨n % 3, by omega⟩

/-- The hospitals of the counterexample. -/
def cxHospital (i : Fin 4) : Prop := i = 3

lemma cx_check : ∀ i x : Fin 4, i ≠ x → (i = 3 ∨ x ≠ 3) → ∃ a b c d : Fin 4,
    (∀ j, ![a, b, c, d] j ≠ j) ∧ (∀ j, j ≠ i → j = 3 ∨ ![a, b, c, d] j ≠ 3) ∧
    ∀ y, y ≠ i → y ≠ x →
      utilF cxα i (update ![a, b, c, d] i y) < utilF cxα i (update ![a, b, c, d] i x) := by
  decide

instance (α : ι → ι → ℕ) (i j : ι) : (o : Option ι) → Decidable (Prefers α i j o)
  | none => isTrue trivial
  | some k => inferInstanceAs (Decidable (α i k < α i j))

lemma cx_noStable : ∀ a b c d : Option (Fin 4),
    ¬ IsStable (· ≠ ·) cxα ![a, b, c, d] := by
  unfold IsStable IsMatching
  decide

/-- **Counterexample to Theorem 3.1 for intern–hospital matchings in the paper's game**, where
every student may propose to every other student (`acc = (· ≠ ·)`). Three interns with cyclic
preferences and one hospital (ranked last by everybody): the hypothesis "all hospitals have the same
ranking of interns" holds, but the game has a ranking cycle, is not NBR-solvable for any
(irreflexive) tie-breaking rule, and has no stable matching at all. -/
theorem internHospital_counterexample :
    (∀ h h' i j, cxHospital h → cxHospital h' → ¬ cxHospital i → ¬ cxHospital j →
      (cxα h i < cxα h j ↔ cxα h' i < cxα h' j)) ∧
    (∀ i j : Fin 4, i ≠ j → 0 < cxα i j) ∧
    (∀ i j k : Fin 4, i ≠ j → i ≠ k → cxα i j = cxα i k → j = k) ∧
    ¬ CycleFree (· ≠ ·) cxα ∧
    (∀ prec : ∀ i, Strat (· ≠ ·) i → Strat (· ≠ ·) i → Prop, (∀ i, Std.Irrefl (prec i)) →
      ¬ (game (· ≠ ·) cxα prec).NBRSolvable) ∧
    ∀ m, ¬ IsStable (· ≠ ·) cxα m := by
  refine ⟨?_, by decide, by decide, ?_, ?_, ?_⟩
  · intro h h' i j hh hh' _ _
    rw [cxHospital] at hh hh'
    rw [hh, hh']
  · intro hcf
    have h3 : ∀ m < 3, cxCyc m ≠ cxCyc (m + 1) ∧
        cxα (cxCyc (m + 1)) (cxCyc m) < cxα (cxCyc (m + 1)) (cxCyc (m + 2)) := by decide
    have e : ∀ i j, cxCyc (i % 3 + j) = cxCyc (i + j) := fun i j => by
      apply Fin.ext; simp only [cxCyc]; omega
    refine hcf 3 cxCyc (by norm_num) (fun i => Fin.ext (by simp [cxCyc])) ?_ (fun i => ?_)
    · intro a ha b hb hab
      simp only [mem_Iio] at ha hb
      have := congrArg Fin.val hab
      simp only [cxCyc] at this
      omega
    · have := h3 (i % 3) (Nat.mod_lt _ (by norm_num))
      rw [e, e, show i % 3 = i % 3 + 0 by rfl, e, add_zero] at this
      exact this
  · intro prec hirr
    refine not_nbrSolvable_of_isBR _ (fun i => {x | i = 3 ∨ x.1 ≠ 3}) ?_
      (i := 0) (x := ⟨1, by decide⟩) (y := ⟨2, by decide⟩) (Or.inr (by decide))
      (Or.inr (by decide)) (by decide)
    intro i x hx
    obtain ⟨a, b, c, d, hf, hH, hlt⟩ := cx_check i x.1 x.2 hx
    refine ⟨fun j => ⟨![a, b, c, d] j, (hf j).symm⟩, fun j hj => hH j hj, ?_⟩
    intro y hy
    by_cases hyx : y = x
    · subst hyx
      rcases hy with h | h
      · exact lt_irrefl _ h
      · exact (hirr i).irrefl _ h.2
    · have := hlt y.1 (Ne.symm y.2) (fun h => hyx (Subtype.ext h))
      change util _ _ i _ < util _ _ i _ ∨ (util _ _ i _ = util _ _ i _ ∧ _) at hy
      rw [util_eq_utilF, util_eq_utilF, val_update, val_update] at hy
      rcases hy with h | h
      · exact absurd this (not_lt.2 h.le)
      · exact absurd this (not_lt.2 h.1.le)
  · intro m hm
    have : m = ![m 0, m 1, m 2, m 3] := by
      funext i; fin_cases i <;> rfl
    rw [this] at hm
    exact cx_noStable _ _ _ _ hm

end Counterexample

end Podc.BestResponseMechanisms.StableRoommates
