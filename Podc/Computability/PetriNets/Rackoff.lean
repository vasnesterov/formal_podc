/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Computability/PetriNets/Rackoff.lean
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rackoff's bound on covering sequences of Petri nets

A Petri net (vector addition system with states-as-places) has finitely many places `P` and
transitions `τ`, each transition `t` consuming `pre t p` and producing `post t p` tokens in place
`p`. We work with *integer* vectors `v : P → ℤ` and a set `I` of *tracked* places: a sequence of
transitions is `I`-valid from `v` if before each step the tracked coordinates are at least `pre`;
the untracked coordinates may become negative. This is the relaxation used by Rackoff (*The
covering and boundedness problems for vector addition systems*, TCS 1978).

## Main definitions

* `PetriNet P τ`: places `P`, transitions `τ`, `pre`, `post : τ → P → ℕ`.
* `N.fire t v`, `N.run w v`: the vector after firing `t`, resp. the sequence `w`, from `v`.
* `N.Valid I w v`: `w` is `I`-valid from `v`.
* `N.Covers I w v u`: the final vector of `w` from `v` is `≥ u` on `I`.
* `rackoffBound M R k`: `g 0 = 0`, `g (k + 1) = (M * g k + R) ^ (k + 1) + g k`.

## Main statements

* `PetriNet.exists_short_cover`: **Rackoff's lemma.** If every `pre t p ≤ M` and
  `u ≤ R`, then every `I`-valid `I`-covering sequence from `v` has a sublist which is again
  `I`-valid and `I`-covering from `v`, of length at most `rackoffBound M R I.card`.
* `rackoffBound_two_two_le`: `rackoffBound 2 2 k ≤ 2 ^ (2 * (2 * k + 1)!)`.
-/

namespace Cslib

/-- A Petri net with places `P` and transitions `τ`: transition `t` consumes `pre t p` and
produces `post t p` tokens in place `p`. -/
structure PetriNet (P τ : Type*) where
  /-- Tokens consumed by a transition. -/
  pre : τ → P → ℕ
  /-- Tokens produced by a transition. -/
  post : τ → P → ℕ

namespace PetriNet

variable {P τ : Type*} (N : PetriNet P τ)

/-- The vector obtained by firing `t` from `v` (no enabledness check). -/
def fire (t : τ) (v : P → ℤ) : P → ℤ := fun p => v p - N.pre t p + N.post t p

/-- The vector obtained by firing the sequence `w` from `v` (no enabledness check). -/
def run : List τ → (P → ℤ) → P → ℤ
  | [], v => v
  | t :: w, v => run w (N.fire t v)

/-- `w` is `I`-valid from `v`: before each step, every place of `I` holds at least `pre`. -/
def Valid (I : Finset P) : List τ → (P → ℤ) → Prop
  | [], _ => True
  | t :: w, v => (∀ p ∈ I, (N.pre t p : ℤ) ≤ v p) ∧ Valid I w (N.fire t v)

/-- `w` `I`-covers `u` from `v`: the final vector is at least `u` on `I`. -/
def Covers (I : Finset P) (w : List τ) (v : P → ℤ) (u : P → ℕ) : Prop :=
  ∀ p ∈ I, (u p : ℤ) ≤ N.run w v p

variable {N}

@[simp] theorem run_nil (v : P → ℤ) : N.run [] v = v := rfl

@[simp] theorem run_cons (t : τ) (w : List τ) (v : P → ℤ) :
    N.run (t :: w) v = N.run w (N.fire t v) := rfl

@[simp] theorem valid_nil (I : Finset P) (v : P → ℤ) : N.Valid I [] v := trivial

@[simp] theorem valid_cons {I : Finset P} {t : τ} {w : List τ} {v : P → ℤ} :
    N.Valid I (t :: w) v ↔ (∀ p ∈ I, (N.pre t p : ℤ) ≤ v p) ∧ N.Valid I w (N.fire t v) :=
  Iff.rfl

theorem run_append (a b : List τ) (v : P → ℤ) : N.run (a ++ b) v = N.run b (N.run a v) := by
  induction a generalizing v with
  | nil => rfl
  | cons t a ih => exact ih _

theorem valid_append {I : Finset P} {a b : List τ} {v : P → ℤ} :
    N.Valid I (a ++ b) v ↔ N.Valid I a v ∧ N.Valid I b (N.run a v) := by
  induction a generalizing v with
  | nil => simp
  | cons t a ih => simp [ih, and_assoc]

/-- Firing shifts differences of vectors unchanged. -/
theorem run_sub_run (w : List τ) (v v' : P → ℤ) (p : P) :
    N.run w v' p - N.run w v p = v' p - v p := by
  induction w generalizing v v' with
  | nil => rfl
  | cons t w ih => rw [run_cons, run_cons, ih]; simp only [fire]; ring

/-- Running is monotone in the initial vector, coordinatewise. -/
theorem run_mono {w : List τ} {v v' : P → ℤ} {p : P} (h : v p ≤ v' p) :
    N.run w v p ≤ N.run w v' p := by
  have := run_sub_run (N := N) w v v' p
  omega

/-- Validity is monotone in the initial vector (only the coordinates in `I` matter). -/
theorem Valid.mono {I : Finset P} {w : List τ} {v v' : P → ℤ} (hw : N.Valid I w v)
    (h : ∀ p ∈ I, v p ≤ v' p) : N.Valid I w v' := by
  induction w generalizing v v' with
  | nil => trivial
  | cons t w ih =>
    refine ⟨fun p hp => (hw.1 p hp).trans (h p hp), ih hw.2 fun p hp => ?_⟩
    simp only [fire]
    linarith [h p hp]

/-- Covering is monotone in the initial vector. -/
theorem Covers.mono {I : Finset P} {w : List τ} {v v' : P → ℤ} {u : P → ℕ}
    (hw : N.Covers I w v u) (h : ∀ p ∈ I, v p ≤ v' p) : N.Covers I w v' u :=
  fun p hp => (hw p hp).trans (run_mono (h p hp))

theorem Valid.subset {I J : Finset P} {w : List τ} {v : P → ℤ} (hw : N.Valid I w v)
    (hJ : J ⊆ I) : N.Valid J w v := by
  induction w generalizing v with
  | nil => trivial
  | cons t w ih => exact ⟨fun p hp => hw.1 p (hJ hp), ih hw.2⟩

theorem Covers.subset {I J : Finset P} {w : List τ} {v : P → ℤ} {u : P → ℕ}
    (hw : N.Covers I w v u) (hJ : J ⊆ I) : N.Covers J w v u :=
  fun p hp => hw p (hJ hp)

/-- The tracked coordinates are nonnegative before a nonempty valid sequence. -/
theorem Valid.nonneg {I : Finset P} {w : List τ} {v : P → ℤ} (hw : N.Valid I w v)
    (hne : w ≠ []) {p : P} (hp : p ∈ I) : 0 ≤ v p := by
  cases w with
  | nil => exact absurd rfl hne
  | cons t w => exact (Int.natCast_nonneg _).trans (hw.1 p hp)

section Bounded

variable {M : ℕ} (hM : ∀ t p, N.pre t p ≤ M)
include hM

/-- Each step consumes at most `M` tokens from each place. -/
theorem run_ge (w : List τ) (v : P → ℤ) (p : P) :
    v p - M * w.length ≤ N.run w v p := by
  induction w generalizing v with
  | nil => simp
  | cons t w ih =>
    have h1 := ih (N.fire t v)
    have h2 : (N.pre t p : ℤ) ≤ M := by exact_mod_cast hM t p
    simp only [run_cons, fire, List.length_cons, Nat.cast_add, Nat.cast_one] at h1 ⊢
    nlinarith [Int.natCast_nonneg (N.post t p)]

/-- A place holding at least `M · |w|` tokens can be added to the tracked set. -/
theorem Valid.insert_of_le [DecidableEq P] {I : Finset P} {w : List τ} {v : P → ℤ} {p : P}
    (hw : N.Valid I w v) (hp : (M * w.length : ℤ) ≤ v p) : N.Valid (insert p I) w v := by
  induction w generalizing v with
  | nil => trivial
  | cons t w ih =>
    have h2 : (N.pre t p : ℤ) ≤ M := by exact_mod_cast hM t p
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hp
    refine ⟨fun q hq => ?_, ih hw.2 ?_⟩
    · rcases Finset.mem_insert.1 hq with rfl | hq
      · nlinarith [Int.natCast_nonneg M, Int.natCast_nonneg w.length]
      · exact hw.1 q hq
    · simp only [fire]
      nlinarith [Int.natCast_nonneg (N.post t p)]

end Bounded

/-- **Loop cutting.** If the tracked coordinates coincide after `a` and after `a ++ b`, then
`b` can be removed from a valid covering sequence `a ++ b ++ c`. -/
theorem cut_loop {I : Finset P} {a b c : List τ} {v : P → ℤ} {u : P → ℕ}
    (hv : N.Valid I (a ++ b ++ c) v) (hc : N.Covers I (a ++ b ++ c) v u)
    (heq : ∀ p ∈ I, N.run (a ++ b) v p = N.run a v p) :
    N.Valid I (a ++ c) v ∧ N.Covers I (a ++ c) v u := by
  rw [valid_append] at hv
  have hle : ∀ p ∈ I, N.run (a ++ b) v p ≤ N.run a v p := fun p hp => (heq p hp).le
  refine ⟨valid_append.2 ⟨(valid_append.1 hv.1).1, hv.2.mono hle⟩, fun p hp => ?_⟩
  have := hc p hp
  rw [run_append] at this ⊢
  exact this.trans (run_mono (hle p hp))

/-- Rackoff's bound: `g 0 = 0`, `g (k + 1) = (M * g k + R) ^ (k + 1) + g k`. -/
def rackoffBound (M R : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (M * rackoffBound M R k + R) ^ (k + 1) + rackoffBound M R k

/-- **Pigeonhole.** If `m` vectors have their `I`-coordinates in `[0, B)` and pairwise differ
on `I`, then `m ≤ B ^ |I|`. -/
theorem card_le_pow_of_distinct {I : Finset P} {B m : ℕ} (f : ℕ → P → ℤ)
    (hb : ∀ i < m, ∀ p ∈ I, 0 ≤ f i p ∧ f i p < B)
    (hd : ∀ i j, i < j → j < m → ¬ ∀ p ∈ I, f i p = f j p) : m ≤ B ^ I.card := by
  classical
  let g : ℕ → (I → ℤ) := fun i p => f i p
  have hmaps : ∀ i ∈ Finset.range m,
      g i ∈ Fintype.piFinset (fun _ : I => Finset.Ico (0 : ℤ) B) := by
    intro i hi
    rw [Fintype.mem_piFinset]
    intro p
    have := hb i (Finset.mem_range.1 hi) p p.2
    simpa [g] using this
  have hinj : Set.InjOn g (Finset.range m) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have hall : ∀ p ∈ I, f i p = f j p := fun p hp => congrFun hij ⟨p, hp⟩
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact hd i j h hj hall
    · exact hd j i h hi fun p hp => (hall p hp).symm
  have := Finset.card_le_card_of_injOn g hmaps hinj
  simpa [Fintype.card_piFinset, Finset.prod_const] using this

/-- The tracked coordinates at every position of a valid covering sequence are nonnegative. -/
theorem nonneg_of_valid_covers {I : Finset P} {w : List τ} {v : P → ℤ} {u : P → ℕ}
    (hv : N.Valid I w v) (hc : N.Covers I w v u) (i : ℕ) {p : P}
    (hp : p ∈ I) : 0 ≤ N.run (w.take i) v p := by
  rcases Nat.lt_or_ge i w.length with h | h
  · rw [← List.take_append_drop i w, valid_append] at hv
    refine hv.2.nonneg ?_ hp
    simpa [List.drop_eq_nil_iff] using h
  · rw [List.take_of_length_le h]
    exact (Int.natCast_nonneg _).trans (hc p hp)

variable [DecidableEq P] {M R : ℕ} {u : P → ℕ}

/-- Rackoff's lemma for tracked sets of a fixed cardinality `k`. -/
theorem exists_short_cover_aux (hM : ∀ t p, N.pre t p ≤ M) (hu : ∀ p, u p ≤ R)
    (k : ℕ) : ∀ (I : Finset P), I.card = k → ∀ (v : P → ℤ) (w : List τ),
      N.Valid I w v → N.Covers I w v u →
      ∃ w', w'.Sublist w ∧ N.Valid I w' v ∧ N.Covers I w' v u ∧
        w'.length ≤ rackoffBound M R k := by
  induction k with
  | zero =>
    intro I hI v w _ _
    rw [Finset.card_eq_zero] at hI
    subst hI
    exact ⟨[], List.nil_sublist _, trivial, fun p hp => absurd hp (Finset.notMem_empty p),
      le_rfl⟩
  | succ k ihk =>
    intro I hI v w
    induction hn : w.length using Nat.strong_induction_on generalizing w with
    | _ n ihn =>
    intro hv hc
    subst hn
    by_cases hloop : ∃ i j, i < j ∧ j ≤ w.length ∧
        ∀ p ∈ I, N.run (w.take i) v p = N.run (w.take j) v p
    · -- cut the loop between positions `i` and `j`
      obtain ⟨i, j, hij, hj, heq⟩ := hloop
      have hsplit : w.take i ++ (w.take j).drop i ++ w.drop j = w := by
        conv_rhs => rw [← List.take_append_drop j w]
        congr 1
        conv_rhs => rw [← List.take_append_drop i (w.take j)]
        rw [List.take_take, min_eq_left hij.le]
      have htj : w.take i ++ (w.take j).drop i = w.take j := by
        conv_rhs => rw [← List.take_append_drop i (w.take j)]
        rw [List.take_take, min_eq_left hij.le]
      rw [← hsplit] at hv hc
      obtain ⟨hv', hc'⟩ := cut_loop hv hc fun p hp => by rw [htj]; exact (heq p hp).symm
      have hlen : (w.take i ++ w.drop j).length < w.length := by
        simp only [List.length_append, List.length_take, List.length_drop]
        omega
      obtain ⟨w', hsub, h1, h2, h3⟩ := ihn _ hlen _ rfl hv' hc'
      refine ⟨w', hsub.trans ?_, h1, h2, h3⟩
      conv_rhs => rw [← hsplit, List.append_assoc]
      exact (List.sublist_append_right _ _).append_left _
    · push Not at hloop
      set B := M * rackoffBound M R k + R with hB
      have hnn := fun i p (hp : p ∈ I) => nonneg_of_valid_covers (N := N) hv hc i hp
      by_cases hbig : ∃ i, i ≤ w.length ∧ ∃ p ∈ I, (B : ℤ) ≤ N.run (w.take i) v p
      · classical
        let i := Nat.find hbig
        obtain ⟨hi, p, hp, hpB⟩ := Nat.find_spec hbig
        have hmin : ∀ i' < i, ∀ q ∈ I, N.run (w.take i') v q < B := by
          intro i' hi' q hq
          have := Nat.find_min hbig hi'
          push Not at this
          exact this (by omega) q hq
        -- the prefix has at most `B ^ (k + 1)` positions
        have hpre : i ≤ B ^ (k + 1) := by
          rw [← hI]
          refine card_le_pow_of_distinct (fun i' => N.run (w.take i') v) (fun i' hi' q hq =>
            ⟨hnn i' q hq, hmin i' hi' q hq⟩) fun a b hab hb => ?_
          obtain ⟨q, hq, hne⟩ := hloop a b hab (by omega)
          exact fun h => hne (h q hq)
        -- shorten the suffix, ignoring the place `p`
        have hw := List.take_append_drop i w
        have hv2 := hv
        rw [← hw, valid_append] at hv2
        have hc2 : N.Covers (I.erase p) (w.drop i) (N.run (w.take i) v) u := by
          intro q hq
          have := hc q (Finset.mem_of_mem_erase hq)
          rwa [← hw, run_append] at this
        have hcard : (I.erase p).card = k := by rw [Finset.card_erase_of_mem hp, hI]; rfl
        obtain ⟨w₂, hsub, hv₂, hc₂, hlen₂⟩ :=
          ihk (I.erase p) hcard _ _ (hv2.2.subset (Finset.erase_subset p I)) hc2
        have hMlen : (M * w₂.length : ℤ) ≤ M * rackoffBound M R k := by
          exact_mod_cast Nat.mul_le_mul_left M hlen₂
        refine ⟨w.take i ++ w₂, ?_, ?_, ?_, ?_⟩
        · conv_rhs => rw [← hw]
          exact hsub.append_left _
        · refine valid_append.2 ⟨hv2.1, ?_⟩
          have := hv₂.insert_of_le hM (p := p) (by push_cast [hB] at hpB; linarith)
          rwa [Finset.insert_erase hp] at this
        · intro q hq
          rw [run_append]
          by_cases hqp : q = p
          · subst hqp
            have := run_ge hM w₂ (N.run (w.take i) v) q
            have huR : (u q : ℤ) ≤ R := by exact_mod_cast hu q
            push_cast [hB] at hpB
            linarith
          · exact hc₂ q (Finset.mem_erase.2 ⟨hqp, hq⟩)
        · simp only [List.length_append, List.length_take, rackoffBound, ← hB]
          have : min i w.length ≤ i := min_le_left _ _
          omega
      · -- all positions are bounded
        push Not at hbig
        refine ⟨w, List.Sublist.refl w, hv, hc, ?_⟩
        have : w.length + 1 ≤ B ^ (k + 1) := by
          rw [← hI]
          refine card_le_pow_of_distinct (fun i' => N.run (w.take i') v) (fun i' hi' q hq =>
            ⟨hnn i' q hq, hbig i' (by omega) q hq⟩) fun a b hab hb => ?_
          obtain ⟨q, hq, hne⟩ := hloop a b hab (by omega)
          exact fun h => hne (h q hq)
        simp only [rackoffBound, ← hB]
        omega

/-- **Rackoff's lemma.** Let every transition consume at most `M` tokens from each place, and
let `u ≤ R`. If `w` is `I`-valid and `I`-covers `u` from `v`, then some sublist of
`w` of length at most `rackoffBound M R |I|` is `I`-valid and `I`-covers `u` from `v`. -/
theorem exists_short_cover (hM : ∀ t p, N.pre t p ≤ M) (hu : ∀ p, u p ≤ R)
    {I : Finset P} {v : P → ℤ} {w : List τ} (hv : N.Valid I w v) (hc : N.Covers I w v u) :
    ∃ w', w'.Sublist w ∧ N.Valid I w' v ∧ N.Covers I w' v u ∧
      w'.length ≤ rackoffBound M R I.card :=
  exists_short_cover_aux hM hu _ I rfl v w hv hc

end PetriNet

/-- An explicit estimate of Rackoff's bound for `M = R = 2`. -/
theorem rackoffBound_two_two_le (k : ℕ) :
    PetriNet.rackoffBound 2 2 k ≤ 2 ^ (2 * (2 * k + 1).factorial) := by
  induction k with
  | zero => simp [PetriNet.rackoffBound]
  | succ k ih =>
    set a := 2 * (2 * k + 1).factorial with ha
    have ha2 : 2 ≤ a := by have := Nat.factorial_pos (2 * k + 1); omega
    have hfac : 2 * (2 * (k + 1) + 1).factorial = (2 * k + 3) * (2 * k + 2) * a := by
      rw [ha, show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring, Nat.factorial_succ,
        Nat.factorial_succ]
      ring
    have h1 : 2 * PetriNet.rackoffBound 2 2 k + 2 ≤ 2 ^ (a + 2) := by
      have : 2 ≤ 2 ^ (a + 1) := Nat.le_self_pow (by omega) 2
      rw [pow_succ, pow_succ] at *
      omega
    have h2 : (2 * PetriNet.rackoffBound 2 2 k + 2) ^ (k + 1) ≤ 2 ^ ((a + 2) * (k + 1)) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left h1 _
    have h3 : (a + 2) * (k + 1) + 1 ≤ (2 * k + 3) * (2 * k + 2) * a := by
      have e : (2 * k + 3) * (2 * k + 2) * a = (k + 1) * (2 * (2 * k + 3) * a) := by ring
      have h5 : a + 3 ≤ 2 * (2 * k + 3) * a := by nlinarith
      rw [e]; nlinarith
    have h4 : a ≤ (a + 2) * (k + 1) := by nlinarith
    simp only [PetriNet.rackoffBound]
    rw [hfac]
    calc (2 * PetriNet.rackoffBound 2 2 k + 2) ^ (k + 1) + PetriNet.rackoffBound 2 2 k
        ≤ 2 ^ ((a + 2) * (k + 1)) + 2 ^ ((a + 2) * (k + 1)) :=
          add_le_add h2 (ih.trans (Nat.pow_le_pow_right (by omega) h4))
      _ = 2 ^ ((a + 2) * (k + 1) + 1) := by rw [pow_succ]; ring
      _ ≤ 2 ^ ((2 * k + 3) * (2 * k + 2) * a) := Nat.pow_le_pow_right (by omega) h3

end Cslib
