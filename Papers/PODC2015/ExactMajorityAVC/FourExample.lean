import Papers.PODC2015.ExactMajorityAVC.FourMain
import Papers.PODC2015.ExactMajorityAVC.AVCCorrect

/-!
# Non-vacuity: the classical four-state protocol satisfies the hypotheses of Theorem B.1

The four-state protocol of Draief–Vojnović / Mertzios et al. (Case 1.1 of the paper, and AVC with
`m = d = 1`): `[S0, S1] → [X, Y]`, `[S0, Y] → [S0, X]`, `[S1, X] → [S1, Y]`, all other pairs
unchanged; output `γ(S0) = γ(X) = 0`, `γ(S1) = γ(Y) = 1`.

`std_correct` proves the three correctness properties for every population size, so the
hypotheses of `theorem_B_1_invariant` are satisfiable.
-/

namespace Podc.ExactMajorityAVC.Four

open Cslib.PopulationProtocol Q4 Multiset

/-- The classical four-state exact majority protocol. -/
def std : Protocol Q4 where
  δ p q := match p, q with
    | S0, S1 => (X, Y)
    | S1, S0 => (Y, X)
    | S0, Y => (S0, X)
    | Y, S0 => (X, S0)
    | S1, X => (S1, Y)
    | X, S1 => (Y, S1)
    | p, q => (p, q)

/-- `x i`: the non-initial state with output `i`. -/
def xs : Bool → Q4
  | false => X
  | true => Y

theorem std_symmetric : Symmetric std := by
  intro p q; cases p <;> cases q <;> decide

theorem std_invariant : Invariant std := by
  intro p q; cases p <;> cases q <;> decide

lemma gammaA_S (i : Bool) : gammaA (S i) = i := by cases i <;> rfl
lemma gammaA_xs (i : Bool) : gammaA (xs i) = i := by cases i <;> rfl

lemma std_st (i : Bool) : pair (std.δ (S i) (S !i)) = {xs i, xs !i} := by cases i <;> decide
lemma std_sy (i : Bool) : pair (std.δ (S i) (xs !i)) = {S i, xs i} := by cases i <;> decide
lemma std_same (i : Bool) {p q : Q4} (hp : gammaA p = i) (hq : gammaA q = i) :
    std.δ p q = (p, q) := by
  cases i <;> cases p <;> cases q <;> simp_all [gammaA] <;> rfl

/-- `#S i − #S (!i)`. -/
def diffI (i : Bool) (c : Multiset Q4) : ℤ := (count (S i) c : ℤ) - count (S !i) c

lemma diffI_eq (i : Bool) (c : Multiset Q4) : diffI i c = if i then -diff c else diff c := by
  cases i <;> simp [diffI, diff]

lemma diffI_reach (i : Bool) {c c' : Multiset Q4} (h : Reach std c c') : diffI i c' = diffI i c := by
  rw [diffI_eq, diffI_eq, std_invariant.reach h]

/-- Configurations whose states all have output `i` are absorbing. -/
lemma absorbing_of_all (i : Bool) {c : Multiset Q4} (hc : ∀ q ∈ c, gammaA q = i) :
    Absorbing std gammaA i c := by
  have key : ∀ c', Reach std c c' → c' = c := by
    intro c' h
    induction h with
    | refl => rfl
    | tail _ hs ih =>
      subst ih
      obtain ⟨p, q, r, hc', rfl⟩ := exists_of_step hs
      rw [hc'] at hc ⊢
      rw [std_same i (hc p (by simp)) (hc q (by simp))]
  intro c' h
  rw [key c' h]; exact hc

lemma step_pair_std {p q : Q4} {m' : Multiset Q4} (h : pair (std.δ p q) = m') (r : Multiset Q4) :
    MStep (trans std) (p ::ₘ q ::ₘ r) (m' + r) := by
  have := step_pair (P := std) (m := {p, q}) rfl h r
  simpa [insert_eq_cons] using this

/-- From every configuration with `#S i > #S (!i)` an all-`i` configuration is reachable. -/
lemma std_reach (i : Bool) (c : Multiset Q4) (hc : 0 < diffI i c) :
    ∃ c', Reach std c c' ∧ ∀ q ∈ c', gammaA q = i := by
  -- phase 1: remove `S (!i)`
  obtain ⟨c1, h1, -, hg1⟩ := reach_of_measure (R := MStep (trans std))
    (fun c => 0 < diffI i c) (fun c => count (S !i) c = 0) (fun c => count (S !i) c)
    (fun c hc hg => by
      have hs : S i ∈ c := by
        rw [← count_pos]; unfold diffI at hc; omega
      have ht : S (!i) ∈ c := by rw [← count_pos]; omega
      obtain ⟨r, rfl⟩ := exists_cons_of_mem hs
      have ht' : S (!i) ∈ r := by
        rcases mem_cons.1 ht with h | h
        · cases i <;> simp at h
        · exact h
      obtain ⟨r', rfl⟩ := exists_cons_of_mem ht'
      refine ⟨_, .single (step_pair_std (std_st i) r'), ?_, ?_⟩
      · rw [diffI_reach i (.single (step_pair_std (std_st i) r'))]; exact hc
      · cases i <;> simp [insert_eq_cons, xs]) c hc
  -- phase 2: turn `x (!i)` into `x i`
  obtain ⟨c2, h2, ⟨-, hg2⟩, hg2'⟩ := reach_of_measure (R := MStep (trans std))
    (fun c => 0 < diffI i c ∧ count (S !i) c = 0) (fun c => count (xs !i) c = 0)
    (fun c => count (xs !i) c)
    (fun c ⟨hc, hc0⟩ hg => by
      have hs : S i ∈ c := by
        rw [← count_pos]; unfold diffI at hc; omega
      have hy : xs (!i) ∈ c := by rw [← count_pos]; omega
      obtain ⟨r, rfl⟩ := exists_cons_of_mem hs
      have hy' : xs (!i) ∈ r := by
        rcases mem_cons.1 hy with h | h
        · cases i <;> simp [xs] at h
        · exact h
      obtain ⟨r', rfl⟩ := exists_cons_of_mem hy'
      have hst := step_pair_std (std_sy i) r'
      refine ⟨_, .single hst, ⟨?_, ?_⟩, ?_⟩
      · rw [diffI_reach i (.single hst)]; exact hc
      · cases i <;> simp_all [insert_eq_cons, xs]
      · cases i <;> simp [insert_eq_cons, xs]) c1
    ⟨by rw [diffI_reach i h1]; exact hc, hg1⟩
  refine ⟨c2, h1.trans h2, fun q hq => ?_⟩
  have : q ≠ S (!i) := by rintro rfl; exact (count_eq_zero.1 hg2) hq
  have : q ≠ xs (!i) := by rintro rfl; exact (count_eq_zero.1 hg2') hq
  cases i <;> cases q <;> simp_all [gammaA, xs]

/-- **Non-vacuity of Theorem B.1.** The classical four-state protocol satisfies the three
correctness properties for every population size. -/
theorem std_correct : Correct std gammaA where
  nonempty n _ i := ⟨replicate n (S i), by simp,
    absorbing_of_all i fun q hq => by rw [eq_of_mem_replicate hq]; exact gammaA_S i⟩
  safe i a b hab c hc habs := by
    have hd : 0 < diffI i c := by
      rw [diffI_reach i hc]; cases i <;> simp [diffI, cfg, count_replicate] <;> omega
    have hs : S i ∈ c := by rw [← count_pos]; unfold diffI at hd; omega
    have := habs.mem _ hs
    rw [gammaA_S] at this; cases i <;> simp at this
  live i a b hab c hc := by
    have hd : 0 < diffI i c := by
      rw [diffI_reach i hc]; cases i <;> simp [diffI, cfg, count_replicate] <;> omega
    obtain ⟨c', h', hall⟩ := std_reach i c hd
    exact ⟨c', h', absorbing_of_all i hall⟩

end Podc.ExactMajorityAVC.Four
