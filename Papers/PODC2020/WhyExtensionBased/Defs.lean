import Podc.Computability.Distributed.NIS.Layers
import Podc.Computability.Distributed.NIS.Game

/-!
# Why extension-based proofs fail (PODC 2020): task, adversary state, invariants

Alistarh, Aspnes, Ellen, Gelashvili, Zhu, *Why extension-based proofs fail*, Section 5.

* `setAgreement X k`: `k`-set agreement with input (and output) values in `X`.
* `AState`: the state of the adversary during phase 1: the terminations decided so far (`term`, a
  protocol in which every undecided state is active), the number `t` of subdivisions, and the output
  queries answered `none` (`recs`).
* `AInv`: the invariants. `far4`/`far5` are the paper's invariants 4 and 5 (with the vertex set
  `Uset` of `N_t(a)`), `recs` replaces the paper's invariant 6: every descendant of a query answered
  `none` is *protected* (`Prot`), i.e. it has not seen the queried value or it is adjacent to a vertex
  that terminated with another value.
* `subdiv_far`: Lemma 5.4 + Lemma 5.5 (subdividing increases the distances by one).
* `terminate_inv`: terminating a safe vertex keeps the invariants.
-/

namespace Podc.WhyExtensionBased

open Cslib.NIS Cslib.NIS.Subdiv St
open scoped Classical

variable {P X : Type} [DecidableEq P]

/-- `k`-set agreement: every output is the input of some process, and at most `k` different
values are output. -/
def setAgreement (X : Type) (k : ℕ) : Task P X X where
  inputs := Set.univ
  spec x := {y | (∀ i, ∃ j, y i = x j) ∧ (Set.range y).ncard ≤ k}

/-- A configuration does not violate `k`-set agreement (`k ≥ 1`) if all its outputs lie in a set of
at most `k` input values. -/
lemma not_violates [Finite X] {k : ℕ} (hk : 1 ≤ k) {δ : Protocol P X X} {C : Config P X}
    (S : Set X) (hS : S.ncard ≤ k) (hin : ∀ z ∈ S, ∃ j, (C j).input = z)
    (hout : ∀ q z, outs δ C q = some z → z ∈ S) : ¬ Violates (setAgreement X k) δ C := by
  rintro ⟨-, hv⟩
  by_cases hP : IsEmpty P
  · exact hv ⟨fun q => isEmptyElim q, ⟨fun i => isEmptyElim i, by
      rw [Set.range_eq_empty]; simp⟩, fun q => isEmptyElim q⟩
  obtain ⟨j0⟩ := not_isEmpty_iff.1 hP
  obtain ⟨d, hdin, hdS⟩ : ∃ d, (∃ j, (C j).input = d) ∧ (S.Nonempty → d ∈ S) := by
    by_cases hS : S.Nonempty
    · obtain ⟨d, hd⟩ := hS; exact ⟨d, hin d hd, fun _ => hd⟩
    · exact ⟨(C j0).input, ⟨j0, rfl⟩, fun h => absurd h hS⟩
  apply hv
  refine ⟨fun q => (outs δ C q).getD d, ⟨fun i => ?_, ?_⟩, fun q z hz => by simp [hz]⟩
  · cases h : outs δ C i with
    | none => simpa [h, inputs] using hdin.imp fun j hj => hj.symm
    | some z => simpa [h, inputs] using (hin z (hout i z h)).imp fun j hj => hj.symm
  · by_cases hSne : S.Nonempty
    · refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite S)) hS
      rintro _ ⟨q, rfl⟩
      cases h : outs δ C q with
      | none => simpa [h] using hdS hSne
      | some z => simpa [h] using hout q z h
    · have hno : ∀ q, outs δ C q = none := fun q => by
        cases h : outs δ C q with
        | none => rfl
        | some z => exact absurd ⟨z, hout q z h⟩ hSne
      refine le_trans (Set.ncard_le_ncard (t := {d}) ?_ (Set.toFinite _)) (by simpa using hk)
      rintro _ ⟨q, rfl⟩; simp [hno q]

/-! ## Adversary state -/

/-- The state of the adversary in phase 1. -/
structure AState (P X : Type) where
  /-- the terminations decided so far; all other states are (so far) active -/
  term : Protocol P X X
  /-- number of subdivisions: all states of fewer than `t` rounds are decided -/
  t : ℕ
  /-- output queries `(C, Q, y)` answered `none` -/
  recs : List (Config P X × Finset P × X)

/-- `x` is the state of a process of `Q` in a configuration reachable from `C` by a `Q`-only
schedule. -/
def QDesc (δ : Protocol P X X) (C : Config P X) (Q : Finset P) (x : St P X) : Prop :=
  ∃ μ : List P, (∀ p ∈ μ, p ∈ Q) ∧ IsSched δ C μ ∧ ∃ p ∈ Q, exec C μ p = x

/-- `x` is protected against output `y`: it has not seen `y`, or it is adjacent (in its layer) to
a vertex that terminated with another value. -/
def Prot (δ : Protocol P X X) (y : X) (x : St P X) : Prop :=
  ¬ Seen y x ∨ ∃ w b, b ≠ y ∧ decided δ w = some b ∧ Adj δ x.rounds x w

/-- Reached configurations of phase 1: reachable, and every process has done fewer than `t` rounds
or terminated after `t` rounds. -/
def RC (δ : Protocol P X X) (t : ℕ) (C : Config P X) : Prop :=
  Reach δ C ∧ ∀ j, (C j).rounds < t ∨ ((C j).rounds = t ∧ decided δ (C j) ≠ none)

/-- A query `(C, Q, y)` answered `none` stays correct: no `Q`-descendant of `C` has output `y`, and
the undecided ones are protected. -/
def RecOK (δ : Protocol P X X) (t : ℕ) (rec : Config P X × Finset P × X) : Prop :=
  RC δ t rec.1 ∧ ∀ x, QDesc δ rec.1 rec.2.1 x → decided δ x ≠ some rec.2.2 ∧
    (t ≤ x.rounds → x.Settled → decided δ x = none → Prot δ rec.2.2 x)

/-- Terminating `s` with output `a` keeps the distance invariants. -/
def Safe (δ : Protocol P X X) (t : ℕ) (s : St P X) (a : X) : Prop :=
  Far (Adj δ t) {s} (Uset δ t a) 2 ∧ ∀ b, b ≠ a → Far (Adj δ t) {s} (Tset δ t b) 3

/-- The invariants of the adversary in phase 1. -/
structure AInv (A : AState P X) : Prop where
  one_le : 1 ≤ A.t
  dec_le : ∀ s, decided A.term s ≠ none → s.rounds ≤ A.t
  far4 : ∀ a, Far (Adj A.term A.t) (Tset A.term A.t a) (Uset A.term A.t a) 2
  far5 : ∀ a b, a ≠ b → Far (Adj A.term A.t) (Tset A.term A.t a) (Tset A.term A.t b) 3
  recs : ∀ rec ∈ A.recs, RecOK A.term A.t rec

/-! ## Small facts about walks -/

lemma isWalk_pair {G : St P X → St P X → Prop} {u v : St P X} (h : G u v) : IsWalk G [u, v] :=
  ⟨by simp, List.isChain_pair.2 h⟩

lemma isWalk_triple {G : St P X → St P X → Prop} {u v w : St P X} (h : G u v) (h' : G v w) :
    IsWalk G [u, v, w] :=
  ⟨by simp, by simp [List.isChain_cons_cons, h, h']⟩

lemma far_not_adj {G : St P X → St P X → Prop} {A B : Set (St P X)} {d : ℕ} (h : Far G A B d)
    (hd : 2 ≤ d) {u v : St P X} (hu : u ∈ A) (hv : v ∈ B) : ¬ G u v := fun huv => by
  have := h [u, v] (isWalk_pair huv) u (by simp) hu v (by simp) hv
  simp at this; omega

lemma far_not_path2 {G : St P X → St P X → Prop} {A B : Set (St P X)} {d : ℕ} (h : Far G A B d)
    (hd : 3 ≤ d) {u v w : St P X} (hu : u ∈ A) (hw : w ∈ B) (h1 : G u v) (h2 : G v w) : False := by
  have := h [u, v, w] (isWalk_triple h1 h2) u (by simp) hu w (by simp) hw
  simp at this; omega

lemma far_not_mem {G : St P X → St P X → Prop} {A B : Set (St P X)} {d : ℕ} (h : Far G A B d)
    (hd : 1 ≤ d) {u : St P X} (hu : u ∈ A) (hv : u ∈ B) : False := by
  have := h [u] ⟨by simp, List.isChain_singleton u⟩ u (by simp) hu u (by simp) hv
  simp at this; omega

/-- The terminated vertices of the walks of a layer graph. -/
lemma mem_Tset_of_adj {δ : Protocol P X X} {r : ℕ} {u v : St P X} (h : Adj δ r u v) {c : X}
    (hc : decided δ v = some c) : v ∈ Tset δ r c :=
  ⟨h.2.2.1, h.occ_right, hc⟩

lemma mem_Tset_of_adj' {δ : Protocol P X X} {r : ℕ} {u v : St P X} (h : Adj δ r u v) {c : X}
    (hc : decided δ u = some c) : u ∈ Tset δ r c :=
  ⟨h.2.1, h.occ_left, hc⟩

/-! ## Lemma 5.4: every walk from `T(a)` to `U(a) ∪ T(b)` has an edge between active vertices -/

/-- **Lemma 5.4.** -/
lemma actCut_T {δ : Protocol P X X} {t : ℕ} {a : X}
    (h4 : Far (Adj δ t) (Tset δ t a) (Uset δ t a) 2)
    (h5 : ∀ b, b ≠ a → Far (Adj δ t) (Tset δ t a) (Tset δ t b) 3) {B : Set (St P X)}
    (hB : ∀ z ∈ B, z ∈ Uset δ t a ∨ ∃ b, b ≠ a ∧ z ∈ Tset δ t b) :
    ActCut (Adj δ t) (fun s => decided δ s = none) (Tset δ t a) B := by
  intro l
  induction hn : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
  intro hl x0 hx0 hx0T z hz hzB
  match l, hl, hx0, hz with
  | [x0'], hl, hx0, hz =>
    simp at hx0 hz; subst hx0; subst hz
    rcases hB _ hzB with h | ⟨b, hb, h⟩
    · exact (far_not_mem h4 (by omega) hx0T h).elim
    · exact (far_not_mem (h5 b hb) (by omega) hx0T h).elim
  | x0' :: x1 :: rest, hl, hx0, hz =>
    simp at hx0; subst hx0
    have h01 : Adj δ t x0' x1 := (List.isChain_cons_cons.1 hl.2).1
    have htail : IsWalk (Adj δ t) (x1 :: rest) := ⟨by simp, (List.isChain_cons_cons.1 hl.2).2⟩
    have hz' : z ∈ (x1 :: rest).getLast? := by simpa [List.getLast?_cons_cons] using hz
    by_cases hx1 : x1 ∈ Tset δ t a
    · obtain ⟨u, v, huv, hu, hv⟩ := ih _ (by simp at hn ⊢; omega) (x1 :: rest) rfl htail x1 (by simp) hx1 z hz' hzB
      exact ⟨u, v, huv.trans (List.suffix_cons _ _).isInfix, hu, hv⟩
    · -- `x1` is active
      have hx1a : decided δ x1 = none := by
        by_contra hne
        obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hne
        have hT := mem_Tset_of_adj h01 hc
        by_cases hca : c = a
        · subst hca; exact hx1 hT
        · exact far_not_adj (h5 c hca) (by omega) hx0T hT h01
      match rest, htail, hz' with
      | [], _, hz' =>
        simp at hz'; subst hz'
        rcases hB _ hzB with h | ⟨b, hb, h⟩
        · exact (far_not_adj h4 le_rfl hx0T h h01).elim
        · exact (far_not_adj (h5 b hb) (by omega) hx0T h h01).elim
      | x2 :: rest', htail, hz' =>
        have h12 : Adj δ t x1 x2 := (List.isChain_cons_cons.1 htail.2).1
        by_cases hx2 : decided δ x2 = none
        · exact ⟨x1, x2, ⟨[x0'], rest', by simp⟩, hx1a, hx2⟩
        · obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 hx2
          have hT := mem_Tset_of_adj h12 hc
          by_cases hca : c = a
          · subst hca
            have htail2 : IsWalk (Adj δ t) (x2 :: rest') :=
              ⟨by simp, (List.isChain_cons_cons.1 htail.2).2⟩
            obtain ⟨u, v, huv, hu, hv⟩ := ih _ (by simp at hn ⊢; omega) (x2 :: rest') rfl htail2 x2 (by simp) hT z
              (by simpa [List.getLast?_cons_cons] using hz') hzB
            exact ⟨u, v, huv.trans ((List.suffix_cons _ _).trans (List.suffix_cons _ _)).isInfix,
              hu, hv⟩
          · exact (far_not_path2 (h5 c hca) le_rfl hx0T hT h01 h12).elim

/-! ## Lemma 5.5: subdivision -/

/-- **Lemma 5.5** (distance part): if no state of more than `t` rounds is terminated, subdividing
increases the distances between `T(a)` and `U(a)`, and between `T(a)` and `T(b)`, by one. -/
lemma subdiv_far {δ : Protocol P X X} {t d4 d5 : ℕ}
    (h0 : ∀ s, decided δ s ≠ none → s.rounds ≤ t)
    (h4 : ∀ a, Far (Adj δ t) (Tset δ t a) (Uset δ t a) d4)
    (h5 : ∀ a b, a ≠ b → Far (Adj δ t) (Tset δ t a) (Tset δ t b) d5) (hd4 : 2 ≤ d4) (hd5 : 3 ≤ d5) :
    (∀ a, Far (Adj δ (t + 1)) (Tset δ (t + 1) a) (Uset δ (t + 1) a) (d4 + 1)) ∧
    (∀ a b, a ≠ b → Far (Adj δ (t + 1)) (Tset δ (t + 1) a) (Tset δ (t + 1) b) (d5 + 1)) := by
  have hnew : ∀ s : St P X, s.rounds = t + 1 → decided δ s = none := fun s hs => by
    by_contra h; have := h0 s h; omega
  have h4' : ∀ a, Far (Adj δ t) (Tset δ t a) (Uset δ t a) 2 := fun a => (h4 a).mono le_rfl le_rfl hd4
  have h5' : ∀ a b, a ≠ b → Far (Adj δ t) (Tset δ t a) (Tset δ t b) 3 :=
    fun a b h => (h5 a b h).mono le_rfl le_rfl hd5
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · exact far_layer_succ (car_Tset hnew) (car_Uset a) (h4 a)
      (actCut_T (h4' a) (fun b hb => h5' a b (Ne.symm hb)) fun z hz => Or.inl hz)
  · exact far_layer_succ (car_Tset hnew) (car_Tset hnew) (h5 a b hab)
      (actCut_T (h4' a) (fun c hc => h5' a c (Ne.symm hc)) fun z hz => Or.inr ⟨b, Ne.symm hab, hz⟩)

end Podc.WhyExtensionBased
