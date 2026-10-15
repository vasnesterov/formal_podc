import Mathlib
import Cslib.Foundations.SocialChoice.Aggregation

/-!
# Reduction of Arrow's theorem to two voters and three alternatives

Section 5 of S. Rajsbaum, A. Raventós-Pujol, *A Distributed Combinatorial Topology Approach to
Arrow's Impossibility Theorem*, PODC 2022.

* `arrow_of_three` (Lemma 5.1): for any set of voters, Arrow's theorem for `|X| = 3` implies it
  for every `X` with at least three alternatives (`X` may be infinite).
* `arrow_of_two_voters` (Lemma 5.2): for `|X| ≥ 3`, Arrow's theorem for `n = 2` voters implies it
  for every `n ≥ 2`.
* `ArrowHolds.of_equiv`: Arrow's theorem only depends on the set of voters up to bijection.
* `arrow_of_base`: the base case `n = 2`, `|X| = 3` implies Arrow's theorem (Theorem 2.1) for every
  finite set of at least two voters and every set of at least three alternatives.

## Differences with the paper

* Lemma 5.1: the paper's proof that the dictator `k` of the induced map `F̄` on a fixed triple
  `T = {x, y, z}` dictates `F` uses the auxiliary profile `x R' b R' a R' y` / `a R' y R' x R' b`,
  which requires `a, b, x, y` to be pairwise distinct; but `a, b` are arbitrary and `x, y` fixed.
  Repair: `k` dictates every pair inside `T` (via `F̄` and IIA); if `a, b ∈ T` this already
  suffices, otherwise at most one element of `T` lies in `{a, b}` and the construction is run with
  two elements `u ≠ v` of `T \ {a, b}` in place of `x, y`.
* Lemma 5.2, step 3: the paper writes `x F^n(R) z` where `x F^n(R') z` is meant (typo).
-/

universe u

namespace Podc.ArrowTopology

open Cslib.SocialChoice Classical

noncomputable section

/-! ### Helper preferences
General helpers about `Pref` (CSLib candidates). -/

section Helpers

variable {X : Type*}

/-- The preference `a > b > c > (everything else)`. -/
def rank3 (a b c : X) : Pref X :=
  Pref.ofRank fun w => if w = a then 0 else if w = b then 1 else if w = c then 2 else 3

/-- The preference `a > b > c > d > (everything else)`. -/
def rank4 (a b c d : X) : Pref X :=
  Pref.ofRank fun w =>
    if w = a then 0 else if w = b then 1 else if w = c then 2 else if w = d then 3 else 4

/-- In any type with three distinct elements, any two elements can be avoided. -/
theorem exists_ne_ne (hX : ∃ x y z : X, x ≠ y ∧ y ≠ z ∧ x ≠ z) (a b : X) :
    ∃ c, c ≠ a ∧ c ≠ b := by
  obtain ⟨x, y, z, h1, h2, h3⟩ := hX
  by_contra h
  push Not at h
  have hx := h x
  have hy := h y
  have hz := h z
  by_cases hxa : x = a <;> by_cases hya : y = a <;> by_cases hza : z = a <;> grind

end Helpers

/-! ### Lemma 5.1: from three alternatives to any number of alternatives -/

section Lemma51

variable {ι : Type*} {X : Type u}

/-- The aggregation map induced on a subset `S` of alternatives: extend each individual preference
arbitrarily to `X`, aggregate with `F`, and restrict to `S` (well defined up to IIA). -/
def restrictAgg (F : Aggregation ι X) (S : Set X) : Aggregation ι S :=
  fun R => (F fun i => (R i).extend).restrict S

theorem unanimity_restrictAgg {F : Aggregation ι X} (hU : Unanimity F) (S : Set X) :
    Unanimity (restrictAgg F S) := by
  intro R a b h
  show (F fun i => (R i).extend).P a b
  exact hU _ _ _ fun i => (Pref.extend_P_iff _ a b).2 (h i)

theorem iia_restrictAgg {F : Aggregation ι X} (hI : IIA F) (S : Set X) :
    IIA (restrictAgg F S) := by
  intro R R' a b h
  show (F fun i => (R i).extend).P a b ↔ (F fun i => (R' i).extend).P a b
  apply hI
  intro i
  rw [Pref.extend_P_iff, Pref.extend_P_iff]
  exact h i

/-- A dictator of the induced map on `S` dictates `F` on all pairs of elements of `S`. -/
theorem dictates_of_restrictAgg {F : Aggregation ι X} (hI : IIA F) {S : Set X} {k : ι}
    (hk : IsDictator (restrictAgg F S) k) (R : Profile ι X) {a b : X} (ha : a ∈ S) (hb : b ∈ S)
    (hab : (R k).P a b) : (F R).P a b := by
  have h1 : (restrictAgg F S (fun i => (R i).restrict S)).P ⟨a, ha⟩ ⟨b, hb⟩ := hk _ _ _ hab
  refine (hI _ _ a b fun i => ?_).1 h1
  exact Pref.extend_P_iff ((R i).restrict S) ⟨a, ha⟩ ⟨b, hb⟩

set_option linter.unusedSimpArgs false in
/-- Lemma 5.1 of [Rajsbaum–Raventós-Pujol, PODC 2022]. For any set of voters, Arrow's
impossibility theorem for three alternatives implies it for any set `X` of (at least three)
alternatives.

The paper's proof has a gap (the auxiliary profile needs `a, b, x, y` pairwise distinct); it is
repaired here by choosing the auxiliary pair inside the triple, see the module docstring. -/
theorem arrow_of_three (h3 : ∀ Y : Type u, Nat.card Y = 3 → ArrowHolds ι Y)
    (x y z : X) (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : ArrowHolds ι X := by
  intro F hU hI
  set T : Set X := {x, y, z} with hT
  have hcard : Nat.card T = 3 := by
    rw [Nat.card_coe_set_eq]
    exact Set.ncard_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩
  obtain ⟨k, hk⟩ :=
    h3 T hcard (restrictAgg F T) (unanimity_restrictAgg hU T) (iia_restrictAgg hI T)
  -- `k` dictates `F` on all pairs inside the triple `T`.
  have hT2 : ∀ (R : Profile ι X) {u v}, u ∈ T → v ∈ T → (R k).P u v → (F R).P u v :=
    fun R _ _ hu hv h => dictates_of_restrictAgg hI hk R hu hv h
  refine ⟨k, fun R a b hab => ?_⟩
  have hab' : a ≠ b := (R k).ne_of_P hab
  by_cases hin : a ∈ T ∧ b ∈ T
  · exact hT2 R hin.1 hin.2 hab
  -- Gap in the paper: the auxiliary pair must avoid `a` and `b`; pick it inside `T \ {a, b}`.
  obtain ⟨u, v, hu, hv, huv, hua, hub, hva, hvb⟩ :
      ∃ u v, u ∈ T ∧ v ∈ T ∧ u ≠ v ∧ u ≠ a ∧ u ≠ b ∧ v ≠ a ∧ v ≠ b := by
    simp only [hT, Set.mem_insert_iff, Set.mem_singleton_iff] at hin ⊢
    by_cases hx : x = a ∨ x = b
    · exact ⟨y, z, by simp, by simp, hyz, by grind⟩
    · by_cases hy : y = a ∨ y = b
      · exact ⟨x, z, by simp, by simp, hxz, by grind⟩
      · exact ⟨x, y, by simp, by simp, hxy, by grind⟩
  -- `u v` play the roles of the paper's `x y`.
  let R' : Profile ι X := fun i => if (R i).P a b then rank4 a v u b else rank4 u b a v
  have hagree : ∀ i, ((R' i).P a b ↔ (R i).P a b) := by
    intro i
    by_cases h : (R i).P a b
    · simp [R', h, rank4, Pref.ofRank_P_def, hab', hab'.symm, hua, hub, hva, hvb, huv,
        hua.symm, hub.symm, hva.symm, hvb.symm, huv.symm]
    · simp [R', h, rank4, Pref.ofRank_P_def, hab', hab'.symm, hua, hub, hva, hvb, huv,
        hua.symm, hub.symm, hva.symm, hvb.symm, huv.symm]
  have h1 : (F R').P v u := hT2 R' hv hu (by
    simp [R', hab, rank4, Pref.ofRank_P_def, hab', hab'.symm, hua, hub, hva, hvb, huv,
        hua.symm, hub.symm, hva.symm, hvb.symm, huv.symm])
  have h2 : (F R').P a v := hU _ _ _ fun i => by
    by_cases h : (R i).P a b
    · simp [R', h, rank4, Pref.ofRank_P_def, hab', hab'.symm, hua, hub, hva, hvb, huv,
        hua.symm, hub.symm, hva.symm, hvb.symm, huv.symm]
    · simp [R', h, rank4, Pref.ofRank_P_def, hab', hab'.symm, hua, hub, hva, hvb, huv,
        hua.symm, hub.symm, hva.symm, hvb.symm, huv.symm]
  have h3 : (F R').P u b := hU _ _ _ fun i => by
    by_cases h : (R i).P a b
    · simp [R', h, rank4, Pref.ofRank_P_def, hab', hab'.symm, hua, hub, hva, hvb, huv,
        hua.symm, hub.symm, hva.symm, hvb.symm, huv.symm]
    · simp [R', h, rank4, Pref.ofRank_P_def, hab', hab'.symm, hua, hub, hva, hvb, huv,
        hua.symm, hub.symm, hva.symm, hvb.symm, huv.symm]
  exact (hI R' R a b hagree).1 ((F R').trans h2 ((F R').trans h1 h3))

end Lemma51

/-! ### Lemma 5.2: from two voters to any number of voters -/

section Lemma52

variable {X : Type*}

/-- Append a copy of voter `j`'s preference as a new last voter. -/
def appendVoter {m : ℕ} (R : Profile (Fin m) X) (j : Fin m) : Profile (Fin (m + 1)) X :=
  fun i => if h : (i : ℕ) < m then R ⟨i, h⟩ else R j

theorem forall_appendVoter {m : ℕ} (Q : Pref X → Pref X → Prop) {R S : Profile (Fin m) X}
    (j : Fin m) (h : ∀ i, Q (R i) (S i)) (i : Fin (m + 1)) :
    Q (appendVoter R j i) (appendVoter S j i) := by
  unfold appendVoter
  split_ifs <;> exact h _

/-- The `(m)`-voter map obtained from an `(m+1)`-voter map by letting the last voter copy voter
`j` (the paper's `F1^{n-1}`, `F2^{n-1}`). -/
def dropLast {m : ℕ} (F : Aggregation (Fin (m + 1)) X) (j : Fin m) : Aggregation (Fin m) X :=
  fun R => F (appendVoter R j)

theorem unanimity_dropLast {m : ℕ} {F : Aggregation (Fin (m + 1)) X} (hU : Unanimity F)
    (j : Fin m) : Unanimity (dropLast F j) :=
  fun R a b h => hU _ a b (forall_appendVoter (fun A _ => A.P a b) (S := R) j h)

theorem iia_dropLast {m : ℕ} {F : Aggregation (Fin (m + 1)) X} (hI : IIA F) (j : Fin m) :
    IIA (dropLast F j) :=
  fun _ _ a b h => hI _ _ a b (forall_appendVoter (fun A B => A.P a b ↔ B.P a b) j h)

/-- If `k` dictates `dropLast F j`, then `F` follows voter `k` on `a, b` in every profile where
the last voter and voter `j` agree on `a, b`. -/
theorem dropLast_key {m : ℕ} {F : Aggregation (Fin (m + 1)) X} (hI : IIA F) {j k : Fin m}
    (hk : IsDictator (dropLast F j) k) (R : Profile (Fin (m + 1)) X) {a b : X}
    (hjn : (R (Fin.last m)).P a b ↔ (R (Fin.castSucc j)).P a b)
    (hab : (R (Fin.castSucc k)).P a b) : (F R).P a b := by
  have h1 : (F (appendVoter (fun i => R (Fin.castSucc i)) j)).P a b := hk _ a b hab
  refine (hI _ _ a b fun i => ?_).1 h1
  unfold appendVoter
  split_ifs with h
  · exact Iff.rfl
  · have : i = Fin.last m := Fin.ext (by have := i.isLt; simp; omega)
    subst this
    exact hjn.symm

set_option linter.unusedSimpArgs false in
/-- Induction step of Lemma 5.2: Arrow's theorem for `m ≥ 2` voters implies it for `m + 1`. -/
theorem arrow_succ (hX : ∃ x y z : X, x ≠ y ∧ y ≠ z ∧ x ≠ z) {m : ℕ} (hm : 2 ≤ m)
    (h : ArrowHolds (Fin m) X) : ArrowHolds (Fin (m + 1)) X := by
  intro F hU hI
  obtain ⟨i0, i1, h01⟩ : ∃ i0 i1 : Fin m, i0 ≠ i1 :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp⟩
  obtain ⟨k0, hk0⟩ := h _ (unanimity_dropLast hU i0) (iia_dropLast hI i0)
  obtain ⟨k1, hk1⟩ := h _ (unanimity_dropLast hU i1) (iia_dropLast hI i1)
  -- Steps 1 and 2: if the dictator `k` of `dropLast F j` is not `j`, then `k` dictates `F`.
  have step12 : ∀ j k : Fin m, IsDictator (dropLast F j) k → k ≠ j →
      IsDictator F (Fin.castSucc k) := by
    intro j k hk hkj R a b hab
    have hab' : a ≠ b := (R _).ne_of_P hab
    obtain ⟨c, hca, hcb⟩ := exists_ne_ne hX a b
    let R' : Profile (Fin (m + 1)) X := fun i =>
      if i = Fin.castSucc k then rank3 a c b
      else if (R i).P a b then rank3 a b c else rank3 b a c
    have hagree : ∀ i, ((R' i).P a b ↔ (R i).P a b) := by
      intro i
      simp only [R']
      split_ifs with h1 h2
      · subst h1
        simp [hab, rank3, Pref.ofRank_P_def, hab', hab'.symm, hca, hcb, hca.symm, hcb.symm]
      · simp [h2, rank3, Pref.ofRank_P_def, hab', hab'.symm, hca, hcb, hca.symm, hcb.symm]
      · simp [h2, rank3, Pref.ofRank_P_def, hab', hab'.symm, hca, hcb, hca.symm, hcb.symm]
    have h1 : (F R').P c b := by
      refine dropLast_key hI hk R' ?_ ?_
      · have hl : Fin.last m ≠ Fin.castSucc k := (Fin.castSucc_lt_last k).ne'
        have hj : Fin.castSucc j ≠ Fin.castSucc k := by simpa using hkj.symm
        simp only [R', ↓reduceIte, hl, hj]
        split_ifs <;>
          simp [rank3, Pref.ofRank_P_def, hab', hab'.symm, hca, hcb, hca.symm, hcb.symm]
      · simp [R', rank3, Pref.ofRank_P_def, hab', hab'.symm, hca, hcb, hca.symm, hcb.symm]
    have h2 : (F R').P a c := hU _ _ _ fun i => by
      simp only [R']
      split_ifs <;>
        simp [rank3, Pref.ofRank_P_def, hab', hab'.symm, hca, hcb, hca.symm, hcb.symm]
    exact (hI R' R a b hagree).1 ((F R').trans h2 h1)
  rcases eq_or_ne k0 i0 with e0 | e0
  swap
  · exact ⟨_, step12 _ _ hk0 e0⟩
  rcases eq_or_ne k1 i1 with e1 | e1
  swap
  · exact ⟨_, step12 _ _ hk1 e1⟩
  subst e0 e1
  -- Step 3: `dropLast F i0` has dictator `i0` and `dropLast F i1` has dictator `i1`;
  -- then the last voter dictates `F`.
  refine ⟨Fin.last m, fun R a b hab => ?_⟩
  have hab' : a ≠ b := (R _).ne_of_P hab
  obtain ⟨c, hca, hcb⟩ := exists_ne_ne hX a b
  let R' : Profile (Fin (m + 1)) X := fun i =>
    if i = Fin.last m then rank3 a c b
    else if i = Fin.castSucc k0 then (if (R i).P a b then rank3 a c b else rank3 b a c)
    else if i = Fin.castSucc k1 then (if (R i).P a b then rank3 c a b else rank3 c b a)
    else if (R i).P a b then rank3 a b c else rank3 b a c
  have hl0 : Fin.castSucc k0 ≠ Fin.last m := (Fin.castSucc_lt_last k0).ne
  have hl1 : Fin.castSucc k1 ≠ Fin.last m := (Fin.castSucc_lt_last k1).ne
  have h10 : Fin.castSucc k1 ≠ Fin.castSucc k0 := by simpa using h01.symm
  have hagree : ∀ i, ((R' i).P a b ↔ (R i).P a b) := by
    intro i
    rcases eq_or_ne i (Fin.last m) with rfl | hil
    · simp [R', hab, rank3, Pref.ofRank_P_def, hab', hab'.symm, hca, hcb, hca.symm, hcb.symm]
    by_cases h : (R i).P a b
    · simp only [R', ↓reduceIte, hil, h, iff_true]
      split_ifs <;>
        simp [rank3, Pref.ofRank_P_def, hab', hab'.symm, hca, hcb, hca.symm, hcb.symm]
    · simp only [R', ↓reduceIte, hil, h, iff_false]
      split_ifs <;>
        simp [rank3, Pref.ofRank_P_def, hab', hab'.symm, hca, hcb, hca.symm, hcb.symm]
  have h1 : (F R').P a c := by
    refine dropLast_key hI hk0 R' ?_ ?_
    · simp only [R', ↓reduceIte, hl0]
      split_ifs <;>
        simp [rank3, Pref.ofRank_P_def, hab', hab'.symm, hca, hcb, hca.symm, hcb.symm]
    · simp only [R', ↓reduceIte, hl0]
      split_ifs <;>
        simp [rank3, Pref.ofRank_P_def, hab', hab'.symm, hca, hcb, hca.symm, hcb.symm]
  have h2 : (F R').P c b := by
    refine dropLast_key hI hk1 R' ?_ ?_
    · simp only [R', ↓reduceIte, hl1, h10]
      split_ifs <;>
        simp [rank3, Pref.ofRank_P_def, hab', hab'.symm, hca, hcb, hca.symm, hcb.symm]
    · simp only [R', ↓reduceIte, hl1, h10]
      split_ifs <;>
        simp [rank3, Pref.ofRank_P_def, hab', hab'.symm, hca, hcb, hca.symm, hcb.symm]
  exact (hI R' R a b hagree).1 ((F R').trans h1 h2)

/-- Lemma 5.2 of [Rajsbaum–Raventós-Pujol, PODC 2022]. Let `|X| ≥ 3`. If Arrow's theorem holds
for `n = 2` voters, then it holds for every number `n ≥ 2` of voters. -/
theorem arrow_of_two_voters (hX : ∃ x y z : X, x ≠ y ∧ y ≠ z ∧ x ≠ z)
    (h2 : ArrowHolds (Fin 2) X) (n : ℕ) (hn : 2 ≤ n) : ArrowHolds (Fin n) X := by
  induction n, hn using Nat.le_induction with
  | base => exact h2
  | succ m hm ih => exact arrow_succ hX hm ih

end Lemma52

/-! ### Combination -/

/-- Arrow's theorem only depends on the set of voters up to bijection. -/
theorem ArrowHolds.of_equiv {ι κ X : Type*} (e : ι ≃ κ) (h : ArrowHolds ι X) :
    ArrowHolds κ X := by
  intro F hU hI
  let G : Aggregation ι X := fun R => F fun j => R (e.symm j)
  have hGU : Unanimity G := fun R a b hab => hU _ a b fun j => hab _
  have hGI : IIA G := fun R S a b hab => hI _ _ a b fun j => hab _
  obtain ⟨k, hk⟩ := h G hGU hGI
  refine ⟨e k, fun R a b hab => ?_⟩
  have := hk (fun i => R (e i)) a b hab
  simpa [G] using this

/-- Section 5 of [Rajsbaum–Raventós-Pujol, PODC 2022]: the base case (`n = 2` voters, `|X| = 3`
alternatives) implies Arrow's impossibility theorem (Theorem 2.1) for every finite set of at least
two voters and every (possibly infinite) set `X` of at least three alternatives. -/
theorem arrow_of_base {ι : Type*} [Finite ι] {X : Type u}
    (hbase : ∀ Y : Type u, Nat.card Y = 3 → ArrowHolds (Fin 2) Y)
    (hι : 2 ≤ Nat.card ι) (hX : ∃ x y z : X, x ≠ y ∧ y ≠ z ∧ x ≠ z) : ArrowHolds ι X := by
  obtain ⟨x, y, z, hxy, hyz, hxz⟩ := hX
  have h2 : ArrowHolds (Fin 2) X := arrow_of_three hbase x y z hxy hyz hxz
  have hn := arrow_of_two_voters ⟨x, y, z, hxy, hyz, hxz⟩ h2 _ hι
  exact ArrowHolds.of_equiv (Finite.equivFin ι).symm hn

end

end Podc.ArrowTopology
