import Papers.PODC2021.ThinUnison.Observations
import Cslib.Computability.Distributed.SelfStabilization.Unison
import Cslib.Foundations.Combinatorics.SimpleGraph.Spanner
import Mathlib

/-!
# AlgAU: post-stabilization dynamics (Section 2.3.2)

Emek, Keren. *A Thin Self-Stabilizing Asynchronous Unison Algorithm with Applications to Fault
Tolerant Biological Networks*, PODC 2021 ([EK21]).

* Lemma 2.10 of [EK21] (`AURun.allGood_succ`, `AURun.allGood_le`): a good graph stays good.
* Clock lemmas: adjacent levels have clock values differing by at most one (`clock_of_lAdj`), and
  an AA transition increments the clock (`clock_aa`).
* Lemma 2.11 of [EK21] together with safety (`AURun.auFrom_of_allGood`): once the graph is good,
  the execution solves asynchronous unison.

## Proof of liveness

The paper's proof (via Observation 2.8, "`ℓ_min` increases every round") reasons informally about
the cyclic order of the levels. We instead *unwrap* the clocks: fixing a time `t` (at which the
graph is good) and a base node `r`, every node `v` gets an integer offset `o_v` with
`pos(λ_v^t) ≡ pos(λ_r^t) + o_v (mod 2k)` and `|o_u - o_v| ≤ 1` across edges (this uses
`D + 2 ≤ k`). The unwrapped clock `U_v(s) = o_v + #(clock changes of v in [t, s))` keeps both
properties (`AURun.uclk_inv`); hence its spread is at most `D`, and the minimal unwrapped clock
increases by at least one per round (`AURun.uclk_rho`, `AURun.uclk_rho_iter`).
-/

namespace ThinUnison

open Cslib.StoneAge

/-! ## Pure level/clock arithmetic -/

section Pure

variable {k : ℕ}

/-- An AA move of a node at level `a` relative to a neighbour at level `b`. -/
def AAMove (k : ℕ) (a a' b : ℤ) : Prop := a' = a ∨ ((b = a ∨ b = fwd k a) ∧ a' = fwd k a)

/-- Core of Lemma 2.10: AA moves preserve adjacency of levels (including the `{k, -k}` case). -/
theorem lAdj_aaMove {a b a' b' : ℤ} (ha : IsLevel k a) (hb : IsLevel k b) (h : LAdj k a b)
    (ma : AAMove k a a' b) (mb : AAMove k b b' a) : LAdj k a' b' := by
  unfold AAMove at ma mb
  rcases ma with rfl | ⟨h1, rfl⟩ <;> rcases mb with rfl | ⟨h2, rfl⟩ <;>
    (try rcases h1 with rfl | rfl) <;> (try rcases h2 with h2 | h2) <;>
    rcases h with h | h | h <;> lvl_omega

theorem pos_nonneg {ℓ : ℤ} (h : IsLevel k ℓ) : 0 ≤ pos k ℓ := by
  unfold pos; split_ifs <;> lvl_omega

theorem pos_lt {ℓ : ℤ} (h : IsLevel k ℓ) : pos k ℓ < 2 * k := by
  unfold pos; split_ifs <;> lvl_omega

theorem pos_fwd {ℓ : ℤ} (h : IsLevel k ℓ) :
    pos k (fwd k ℓ) = pos k ℓ + 1 ∨ pos k (fwd k ℓ) = pos k ℓ + 1 - 2 * k := by
  unfold pos; split_ifs <;> lvl_omega

theorem pos_of_lAdj {a b : ℤ} (ha : IsLevel k a) (hb : IsLevel k b) (h : LAdj k a b) :
    ∃ δ : ℤ, -1 ≤ δ ∧ δ ≤ 1 ∧ (pos k b = pos k a + δ ∨ pos k b = pos k a + δ + 2 * k ∨
      pos k b = pos k a + δ - 2 * k) := by
  have h1 := pos_nonneg ha; have h2 := pos_nonneg hb
  have h3 := pos_lt ha; have h4 := pos_lt hb
  rcases h with rfl | rfl | rfl
  · exact ⟨0, by omega, by omega, by omega⟩
  · rcases pos_fwd hb with h | h
    · exact ⟨-1, by omega, by omega, by omega⟩
    · exact ⟨-1, by omega, by omega, by omega⟩
  · rcases pos_fwd ha with h | h
    · exact ⟨1, by omega, by omega, by omega⟩
    · exact ⟨1, by omega, by omega, by omega⟩

/-- Integers that are congruent modulo `n` and differ by less than `n` are equal. -/
theorem eq_of_intCast_eq {n : ℕ} {a b : ℤ} (h : (a : ZMod n) = b) (h1 : a - b < n)
    (h2 : b - a < n) : a = b := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  have := Int.eq_zero_of_abs_lt_dvd h (abs_lt.2 ⟨by omega, by omega⟩)
  omega

/-- An AA transition increments the clock: `pos(φ(ℓ)) ≡ pos(ℓ) + 1 (mod 2k)`. -/
theorem pos_fwd_cast {ℓ : ℤ} (h : IsLevel k ℓ) :
    ((pos k (fwd k ℓ) : ℤ) : ZMod (2 * k)) = (pos k ℓ : ZMod (2 * k)) + 1 := by
  rcases pos_fwd h with h | h <;> rw [h]
  · push_cast; ring
  · have : ((2 * k : ℕ) : ZMod (2 * k)) = 0 := ZMod.natCast_self _
    push_cast at this ⊢; rw [this]; ring

/-- Clock values (`pos` modulo `2k`) determine the level. -/
theorem eq_of_pos_cast {a b : ℤ} (ha : IsLevel k a) (hb : IsLevel k b)
    (h : (pos k a : ZMod (2 * k)) = (pos k b : ZMod (2 * k))) : a = b := by
  have h1 := pos_nonneg ha; have h2 := pos_nonneg hb
  have h3 := pos_lt ha; have h4 := pos_lt hb
  have := eq_of_intCast_eq (n := 2 * k) h (by push_cast; omega) (by push_cast; omega)
  unfold pos at this; split_ifs at this <;> lvl_omega

/-- Adjacent levels have clock values differing by at most one (as integers modulo `2k`). -/
theorem pos_cast_of_lAdj {a b : ℤ} (ha : IsLevel k a) (hb : IsLevel k b) (h : LAdj k a b) :
    ∃ δ : ℤ, -1 ≤ δ ∧ δ ≤ 1 ∧
      (pos k b : ZMod (2 * k)) = (pos k a : ZMod (2 * k)) + (δ : ZMod (2 * k)) := by
  obtain ⟨δ, h1, h2, h3⟩ := pos_of_lAdj ha hb h
  refine ⟨δ, h1, h2, ?_⟩
  have : ((2 * k : ℕ) : ZMod (2 * k)) = 0 := ZMod.natCast_self _
  push_cast at this
  rcases h3 with h3 | h3 | h3 <;> rw [h3] <;> push_cast <;> (try rw [this]) <;> ring

theorem two_ne_zero_zmod (hk : 2 ≤ k) : (2 : ZMod (2 * k)) ≠ 0 := by
  intro h
  have := eq_of_intCast_eq (n := 2 * k) (a := 2) (b := 0) (by simpa using h)
    (by push_cast; omega) (by push_cast; omega)
  omega

/-- Adjacent levels have adjacent clock values (the safety condition of AU). -/
theorem clock_of_lAdj {ν μ : Turn k} (h : LAdj k ν.lvl μ.lvl) :
    clock μ = clock ν - 1 ∨ clock μ = clock ν ∨ clock μ = clock ν + 1 := by
  obtain ⟨δ, h1, h2, h3⟩ := pos_cast_of_lAdj ν.isLevel μ.isLevel h
  unfold clock; rw [h3]
  obtain rfl | rfl | rfl : δ = -1 ∨ δ = 0 ∨ δ = 1 := by omega
  · left; push_cast; ring
  · right; left; push_cast; ring
  · right; right; push_cast; ring

/-- An AA transition increments the clock by one. -/
theorem clock_aa (ν : Turn k) : clock ν.aa = clock ν + 1 := pos_fwd_cast ν.isLevel

end Pure

/-! ## Lemma 2.10: a good graph stays good -/

namespace AURun

variable {V : Type*} {G : SimpleGraph V} {k : ℕ} {A : ℕ → Set V} {C : ℕ → V → Turn k}
variable (hC : AURun G A C)
include hC

/-- In a good graph, the only possible transitions are of type AA. -/
theorem good_step {t : ℕ} (hg : AllGood G C t) (v : V) :
    C (t + 1) v = C t v ∨ (v ∈ A t ∧ AAN G C t v ∧ (C (t + 1) v).lvl = fwd k (C t v).lvl ∧
      (C (t + 1) v).faulty = false) := by
  obtain ⟨hp, hf, hn⟩ := hg v
  rcases hC.step_cases t v with h | ⟨h1, -, h2, h3, h4⟩ | ⟨-, -, h2, -⟩ | ⟨-, h2, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3, h4⟩
  · exfalso
    rcases h2.2 with h | ⟨u, hu, h, -⟩
    · exact h hp
    · simp [hn u hu] at h
  · simp [hf] at h2

theorem aaMove_of_good {t : ℕ} (hg : AllGood G C t) {v u : V} (h : G.Adj v u) :
    AAMove k (C t v).lvl (C (t + 1) v).lvl (C t u).lvl := by
  rcases hC.good_step hg v with h1 | ⟨-, h2, h3, -⟩
  · left; rw [h1]
  · right; exact ⟨(h2 u h).2, h3⟩

/-- Lemma 2.10 of [EK21]: if the graph is good at time `t`, it is good at time `t + 1`. -/
theorem allGood_succ {t : ℕ} (hg : AllGood G C t) : AllGood G C (t + 1) := by
  have hf : ∀ v, (C (t + 1) v).faulty = false := fun v => by
    rcases hC.good_step hg v with h | ⟨-, -, -, h⟩
    · rw [h]; exact (hg v).2.1
    · exact h
  refine fun v => ⟨fun u hu => ?_, hf v, fun u _ => hf u⟩
  exact lAdj_aaMove (C t v).isLevel (C t u).isLevel ((hg v).1 u hu) (hC.aaMove_of_good hg hu)
    (hC.aaMove_of_good hg hu.symm)

/-- Lemma 2.10 of [EK21], iterated. -/
theorem allGood_le {t s : ℕ} (hg : AllGood G C t) (hts : t ≤ s) : AllGood G C s := by
  induction s, hts using Nat.le_induction with
  | base => exact hg
  | succ n _ ih => exact hC.allGood_succ ih

end AURun

/-! ## Unwrapped clocks -/

section Unwrap

variable {V : Type*} {G : SimpleGraph V} {k : ℕ} {A : ℕ → Set V} {C : ℕ → V → Turn k}

variable (C) in
/-- The number of output (clock) changes of `v` during `[a, b)`. -/
def nChg (v : V) (a b : ℕ) : ℕ :=
  ((Finset.Ico a b).filter (fun s => output (C (s + 1) v) ≠ output (C s v))).card

variable (C) in
/-- The unwrapped clock of `v` at time `s`, relative to the start time `t` and offsets `o`. -/
def uclk (o : V → ℤ) (t s : ℕ) (v : V) : ℤ := o v + (nChg C v t s : ℤ)

theorem nChg_self (v : V) (a : ℕ) : nChg C v a a = 0 := by simp [nChg]

theorem uclk_self (o : V → ℤ) (t : ℕ) (v : V) : uclk C o t t v = o v := by
  simp [uclk, nChg_self]

theorem nChg_succ (v : V) {a b : ℕ} (hab : a ≤ b) :
    nChg C v a (b + 1) =
      nChg C v a b + if output (C (b + 1) v) ≠ output (C b v) then 1 else 0 := by
  unfold nChg
  rw [Nat.Ico_succ_right_eq_insert_Ico hab, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]; simp
  · rfl

theorem uclk_succ (o : V → ℤ) (v : V) {t s : ℕ} (hts : t ≤ s) :
    uclk C o t (s + 1) v =
      uclk C o t s v + if output (C (s + 1) v) ≠ output (C s v) then 1 else 0 := by
  unfold uclk; rw [nChg_succ v hts]; split_ifs <;> push_cast <;> ring

theorem nChg_mono (v : V) {a b b' : ℕ} (h : b ≤ b') : nChg C v a b ≤ nChg C v a b' :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Ico_subset_Ico le_rfl h))

theorem uclk_mono (o : V → ℤ) (v : V) {t s s' : ℕ} (h : s ≤ s') :
    uclk C o t s v ≤ uclk C o t s' v := by
  unfold uclk; have := nChg_mono (C := C) v (a := t) h; omega

/-- A function that grows by at most one across each edge grows by at most the length along a
walk. -/
theorem le_add_length_of_walk {f : V → ℤ} (hf : ∀ a b, G.Adj a b → f a ≤ f b + 1) {a b : V}
    (p : G.Walk a b) : f a ≤ f b + p.length := by
  induction p with
  | nil => simp
  | cons h q ih => have := hf _ _ h; simp only [SimpleGraph.Walk.length_cons]; push_cast; omega

end Unwrap

namespace AURun

variable {V : Type*} {G : SimpleGraph V} {k : ℕ} {A : ℕ → Set V} {C : ℕ → V → Turn k}
variable (hC : AURun G A C)
include hC

omit hC in
/-- An AA transition between able turns changes the output. -/
theorem output_ne_of_fwd {ν μ : Turn k} (h : μ.lvl = fwd k ν.lvl) (hν : ν.faulty = false)
    (hμ : μ.faulty = false) : output μ ≠ output ν := by
  simp only [output, hν, hμ, Bool.false_eq_true, ite_false, ne_eq, Option.some.injEq]
  unfold clock; rw [h, pos_fwd_cast ν.isLevel]
  intro h4
  exact (ZMod.one_eq_zero_iff (n := 2 * k)).not.2 (by omega) (by simpa using h4)

/-- In a good graph, a node whose output does not change keeps its turn. -/
theorem eq_of_not_chg {s : ℕ} (hg : AllGood G C s) {v : V}
    (h : ¬ output (C (s + 1) v) ≠ output (C s v)) : C (s + 1) v = C s v := by
  rcases hC.good_step hg v with h1 | ⟨-, -, h2, h3⟩
  · exact h1
  · exact absurd (output_ne_of_fwd h2 (hg v).2.1 h3) h

/-- In a good graph, an output change is an AA transition. -/
theorem aa_of_chg {s : ℕ} (hg : AllGood G C s) {v : V}
    (h : output (C (s + 1) v) ≠ output (C s v)) :
    v ∈ A s ∧ AAN G C s v ∧ (C (s + 1) v).lvl = fwd k (C s v).lvl := by
  rcases hC.good_step hg v with h1 | ⟨h1, h2, h3, -⟩
  · rw [h1] at h; exact absurd rfl h
  · exact ⟨h1, h2, h3⟩

/-- In a good graph, an AA transition changes the output. -/
theorem chg_of_aa {s : ℕ} (hg : AllGood G C s) {v : V}
    (h : (C (s + 1) v).lvl = fwd k (C s v).lvl) : output (C (s + 1) v) ≠ output (C s v) :=
  output_ne_of_fwd h (hg v).2.1 (hC.allGood_succ hg v).2.1

/-- The invariant of the unwrapped clocks: from a good time `t` on, the unwrapped clock `U_v(s)`
represents the clock of `v` (relative to the base value `B`), and differs by at most one across
edges. -/
theorem uclk_inv (hk : 2 ≤ k) {t : ℕ} (hg : AllGood G C t) (o : V → ℤ) (B : ZMod (2 * k))
    (h1 : ∀ v, (pos k (C t v).lvl : ZMod (2 * k)) = B + (o v : ZMod (2 * k)))
    (h2 : ∀ u v, G.Adj u v → o u ≤ o v + 1) {s : ℕ} (hs : t ≤ s) :
    (∀ v, (pos k (C s v).lvl : ZMod (2 * k)) = B + (uclk C o t s v : ZMod (2 * k))) ∧
      ∀ u v, G.Adj u v → uclk C o t s u ≤ uclk C o t s v + 1 := by
  induction s, hs using Nat.le_induction with
  | base => simpa [uclk_self] using ⟨h1, h2⟩
  | succ s hs ih =>
    obtain ⟨i1, i2⟩ := ih
    have hgs := hC.allGood_le hg hs
    refine ⟨fun v => ?_, fun u v huv => ?_⟩
    · rw [uclk_succ o v hs]
      by_cases hc : output (C (s + 1) v) ≠ output (C s v)
      · obtain ⟨-, -, h3⟩ := hC.aa_of_chg hgs hc
        rw [ite_eq_left hc, h3, pos_fwd_cast (C s v).isLevel, i1 v]; push_cast; ring
      · rw [ite_eq_right hc, hC.eq_of_not_chg hgs hc, i1 v]; simp
    · rw [uclk_succ o u hs, uclk_succ o v hs]
      have i2' := i2 u v huv
      have i2'' := i2 v u huv.symm
      by_cases hcu : output (C (s + 1) u) ≠ output (C s u)
      · by_cases hcv : output (C (s + 1) v) ≠ output (C s v)
        · simp only [ite_eq_left hcu, ite_eq_left hcv]; omega
        · simp only [ite_eq_left hcu, ite_eq_right hcv]
          by_contra hlt
          have heq : uclk C o t s u = uclk C o t s v + 1 := by omega
          obtain ⟨-, h3, -⟩ := hC.aa_of_chg hgs hcu
          have eu := i1 u
          have ev := i1 v
          rw [heq] at eu
          rcases (h3 v huv).2 with h4 | h4
          · rw [h4, eu] at ev
            exact (ZMod.one_eq_zero_iff (n := 2 * k)).not.2 (by omega)
              (by push_cast at ev; linear_combination ev)
          · rw [h4, pos_fwd_cast (C s u).isLevel, eu] at ev
            exact two_ne_zero_zmod hk (by push_cast at ev; linear_combination ev)
      · simp only [ite_eq_right hcu]; split_ifs <;> omega

/-- A node that is not activated keeps its unwrapped clock. -/
theorem uclk_eq_of_not_mem (o : V → ℤ) {t τ s : ℕ} (htτ : t ≤ τ) (hτs : τ ≤ s) {w : V}
    (h : ∀ s', τ ≤ s' → s' < s → w ∉ A s') : uclk C o t s w = uclk C o t τ w := by
  induction s, hτs using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [uclk_succ o w (htτ.trans hn), hC.succ_of_not_mem (h n hn (Nat.lt_succ_self n)),
      ih fun s' h1 h2 => h s' h1 (by omega)]
    simp

/-- One round increases the minimal unwrapped clock (more precisely: any lower bound `M` on the
unwrapped clocks at time `τ` is exceeded at time `ϱ(τ)`). A node `w` with `U_w(τ) = M` stays at
`M` until its first activation in `[τ, ϱ(τ))`; at that time all its neighbours have unwrapped
clocks `M` or `M + 1`, hence levels `λ_w` or `φ(λ_w)`, so `w` performs an AA transition. -/
theorem uclk_rho [Finite V] (hA : Fair A) (hk : 2 ≤ k) {t : ℕ} (hg : AllGood G C t)
    (o : V → ℤ) (B : ZMod (2 * k))
    (h1 : ∀ v, (pos k (C t v).lvl : ZMod (2 * k)) = B + (o v : ZMod (2 * k)))
    (h2 : ∀ u v, G.Adj u v → o u ≤ o v + 1) {τ : ℕ} (hτ : t ≤ τ) {M : ℤ}
    (hM : ∀ w, M ≤ uclk C o t τ w) (w : V) : M + 1 ≤ uclk C o t (rho A τ) w := by
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := exists_first_act hA w τ
  by_cases hw : M + 1 ≤ uclk C o t τ w
  · exact hw.trans (uclk_mono o w (le_rho hA τ))
  have hwM : uclk C o t τ w = M := by have := hM w; omega
  have hws : uclk C o t s w = M := (hC.uclk_eq_of_not_mem o hτ hs1 hs4).trans hwM
  have hts : t ≤ s := hτ.trans hs1
  have hgs := hC.allGood_le hg hts
  obtain ⟨i1, i2⟩ := hC.uclk_inv hk hg o B h1 h2 hts
  have haan : AAN G C s w := by
    intro u hu
    refine ⟨(hgs u).2.1, ?_⟩
    have l1 : M ≤ uclk C o t s u := (hM u).trans (uclk_mono o u hs1)
    have l2 := i2 u w hu.symm
    have eu := i1 u
    have ew := i1 w
    rw [hws] at ew l2
    obtain h | h : uclk C o t s u = M ∨ uclk C o t s u = M + 1 := by omega
    · left
      exact eq_of_pos_cast (C s u).isLevel (C s w).isLevel (by rw [eu, ew, h])
    · right
      refine eq_of_pos_cast (C s u).isLevel (C s w).aa.isLevel ?_
      rw [pos_fwd_cast (C s w).isLevel, eu, ew, h]
      push_cast; ring
  have hchg := hC.chg_of_aa hgs (hC.succ_aa hs3 (hgs w).2.1 haan).1
  have e := uclk_succ (C := C) o w hts
  rw [ite_eq_left hchg, hws] at e
  rw [← e]
  exact uclk_mono o w (by omega)

/-- `j` rounds increase the minimal unwrapped clock by at least `j`. -/
theorem uclk_rho_iter [Finite V] (hA : Fair A) (hk : 2 ≤ k) {t : ℕ} (hg : AllGood G C t)
    (o : V → ℤ) (B : ZMod (2 * k))
    (h1 : ∀ v, (pos k (C t v).lvl : ZMod (2 * k)) = B + (o v : ZMod (2 * k)))
    (h2 : ∀ u v, G.Adj u v → o u ≤ o v + 1) (j : ℕ) {τ : ℕ} (hτ : t ≤ τ) {M : ℤ}
    (hM : ∀ w, M ≤ uclk C o t τ w) (w : V) : M + j ≤ uclk C o t ((rho A)^[j] τ) w := by
  induction j generalizing τ M with
  | zero => simpa using hM w
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    have := ih (hτ.trans (le_rho hA τ)) (M := M + 1) (hC.uclk_rho hA hk hg o B h1 h2 hτ hM)
    push_cast; linarith

omit hC in
/-- Along a walk of a good graph, clock values change by at most one per edge (cf. Obs. 2.7). -/
theorem pos_walk {t : ℕ} (hg : AllGood G C t) {r w : V} (p : G.Walk r w) :
    ∃ z : ℤ, -(p.length : ℤ) ≤ z ∧ z ≤ p.length ∧
      (pos k (C t w).lvl : ZMod (2 * k)) =
        (pos k (C t r).lvl : ZMod (2 * k)) + (z : ZMod (2 * k)) := by
  induction p with
  | nil => exact ⟨0, by simp, by simp, by simp⟩
  | @cons a b c hab q ih =>
    obtain ⟨z, hz1, hz2, hz⟩ := ih
    obtain ⟨δ, hδ1, hδ2, hδ⟩ := pos_cast_of_lAdj (C t a).isLevel (C t b).isLevel ((hg a).1 b hab)
    refine ⟨δ + z, ?_, ?_, ?_⟩
    · simp only [SimpleGraph.Walk.length_cons]; push_cast; omega
    · simp only [SimpleGraph.Walk.length_cons]; push_cast; omega
    · rw [hz, hδ]; push_cast; ring

omit hC in
/-- Lifting the clocks of a good graph to integers (cf. Obs. 2.8): if `D + 2 ≤ k`, there are
integer offsets `o_v` with `pos(λ_v) ≡ B + o_v (mod 2k)` that differ by at most one across
edges. -/
theorem exists_offsets {d : ℕ} (hd : G.ediam ≤ d) (hdk : d + 2 ≤ k) {t : ℕ} (hg : AllGood G C t)
    (r : V) : ∃ (o : V → ℤ) (B : ZMod (2 * k)),
      (∀ v, (pos k (C t v).lvl : ZMod (2 * k)) = B + (o v : ZMod (2 * k))) ∧
      ∀ u v, G.Adj u v → o u ≤ o v + 1 := by
  have : NeZero (2 * k) := ⟨by omega⟩
  set B : ZMod (2 * k) := (pos k (C t r).lvl : ZMod (2 * k))
  let o : V → ℤ := fun w => ((pos k (C t w).lvl : ZMod (2 * k)) - B).valMinAbs
  have ho : ∀ w, (o w : ZMod (2 * k)) = (pos k (C t w).lvl : ZMod (2 * k)) - B := fun w =>
    ZMod.coe_valMinAbs _
  have hb : ∀ w, -(d : ℤ) ≤ o w ∧ o w ≤ d := by
    intro w
    obtain ⟨p, hp⟩ := SimpleGraph.ediam_le_coe_iff.1 hd r w
    obtain ⟨z, hz1, hz2, hz⟩ := pos_walk hg p
    have h1 : (o w : ZMod (2 * k)) = (z : ZMod (2 * k)) := by rw [ho, hz]; ring
    have h2 := ZMod.natAbs_valMinAbs_le ((pos k (C t w).lvl : ZMod (2 * k)) - B)
    have h3 : (o w).natAbs ≤ k := by
      show (((pos k (C t w).lvl : ZMod (2 * k)) - B).valMinAbs).natAbs ≤ k; omega
    have := eq_of_intCast_eq h1 (by push_cast; omega) (by push_cast; omega)
    omega
  refine ⟨o, B, fun v => by rw [ho]; ring, fun u v huv => ?_⟩
  obtain ⟨δ, hδ1, hδ2, hδ⟩ := pos_cast_of_lAdj (C t u).isLevel (C t v).isLevel ((hg u).1 v huv)
  have h1 : (o v : ZMod (2 * k)) = ((o u + δ : ℤ) : ZMod (2 * k)) := by
    rw [ho, hδ]; push_cast; rw [ho]; ring
  have := hb u; have := hb v
  have := eq_of_intCast_eq h1 (by push_cast; omega) (by push_cast; omega)
  omega

/-- Lemma 2.10, Lemma 2.11 and safety, i.e. "a good graph has stabilized", of [EK21]: if `G`
has diameter at most `D`, `D + 2 ≤ k` and the graph is good at time `T`, then from time `T` on the
execution solves asynchronous unison (all nodes are able; neighbouring clocks differ by at most
one; clocks only advance by `+1`; every node advances its clock at least `i` times during
`[t, ϱ^{D+i}(t))` for every `t ≥ T`). -/
theorem auFrom_of_allGood [Finite V] (hA : Fair A) {d T : ℕ} (hd : G.ediam ≤ d)
    (hk : d + 2 ≤ k) (hT : AllGood G C T) :
    AUFrom G A (output (k := k)) C d T where
  output t ht v := by simp [output, (hC.allGood_le hT ht v).2.1]
  safety t ht u v huv c c' hu hv := by
    have hg := hC.allGood_le hT ht
    simp only [output, (hg u).2.1, (hg v).2.1, Bool.false_eq_true, ite_false,
      Option.some.injEq] at hu hv
    subst hu hv
    exact clock_of_lAdj ((hg u).1 v huv)
  incr t ht v c c' h h' := by
    have hg := hC.allGood_le hT ht
    rcases hC.good_step hg v with h1 | ⟨-, -, h2, h3⟩
    · rw [h1, h] at h'; left; exact (Option.some.inj h').symm
    · right
      simp only [output, (hg v).2.1, h3, Bool.false_eq_true, ite_false,
        Option.some.injEq] at h h'
      subst h h'
      unfold clock; rw [h2, pos_fwd_cast (C t v).isLevel]
  liveness t ht v i := by
    have hg := hC.allGood_le hT ht
    obtain ⟨o, B, h1, h2⟩ := exists_offsets hd hk hg v
    have hM : ∀ w, o v - d ≤ uclk C o t t w := by
      intro w
      obtain ⟨p, hp⟩ := SimpleGraph.ediam_le_coe_iff.1 hd v w
      have := le_add_length_of_walk h2 p
      rw [uclk_self]; omega
    have key := hC.uclk_rho_iter hA (by omega) hg o B h1 h2 (d + i) le_rfl hM v
    show i ≤ nChg C v t _
    unfold uclk at key
    push_cast at key
    omega

end AURun

end ThinUnison
