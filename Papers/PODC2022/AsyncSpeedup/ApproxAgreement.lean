import Papers.PODC2022.AsyncSpeedup.Local
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Abs

/-!
# Approximate agreement (Section 5): tasks, Claim 1, and the closure inclusions

Values are scaled by `m`: the grid `{0, 1/m, …, 1}` of Definition 3 is `{0, …, m} ⊆ ℤ` and the
precision `ε = e/m` becomes the integer `e`. Participating sets are restricted to a set `S` of
processes (`S = univ` for the tasks of the paper; smaller `S` is used in Section 5.3).

* `aa S m e` — Definition 3 (`ε`-approximate agreement), `libAA S m e` — Definition 4 (liberal
  version: no distance constraint when exactly two processes participate).
* `claim1_aa`, `claim1_lib` — Claim 1 (no 0-round algorithm for `ε < 1`).
* `closure_aa_subset` — the inclusion `Δ'_ε ⊆ Δ_{3ε}` of Claim 2 (it holds for any `n`).
* `closure_libAA_subset_of_triangle` — the inclusion `Δ'_ε ⊆ Δ_{2ε}` of Claims 3, 4, 6 for every
  model having the two executions of Figure 6; instantiated in `claim3_subset` (IIS) and
  `claim4_subset` (IIS + test&set).
-/

set_option linter.unusedSectionVars false

namespace AsyncSpeedup

open Cslib.Iterated

variable {P : Type} [DecidableEq P]

/-- `min_{i ∈ I} x_i ≤ v ≤ max_{i ∈ I} x_i`. -/
def InRange (I : Finset P) (x : P → ℤ) (v : ℤ) : Prop :=
  (∃ i ∈ I, x i ≤ v) ∧ ∃ j ∈ I, v ≤ x j

lemma InRange.of_between {I : Finset P} {x : P → ℤ} {a b v : ℤ} (ha : InRange I x a)
    (hb : InRange I x b) (h1 : a ≤ v) (h2 : v ≤ b) : InRange I x v := by
  obtain ⟨⟨i, hi, hia⟩, -⟩ := ha
  obtain ⟨-, ⟨j, hj, hjb⟩⟩ := hb
  exact ⟨⟨i, hi, hia.trans h1⟩, ⟨j, hj, h2.trans hjb⟩⟩

lemma inRange_singleton {i : P} {x : P → ℤ} {v : ℤ} : InRange {i} x v ↔ v = x i := by
  simp only [InRange, Finset.mem_singleton, exists_eq_left]
  omega

/-- Input simplices of approximate agreement: nonempty participating sets inside `S`, inputs on the
grid `{0, …, m}`. -/
def aaInp (S : Finset P) (m : ℤ) : Set (Finset P × (P → ℤ)) :=
  {σ | σ.1.Nonempty ∧ σ.1 ⊆ S ∧ ∀ i ∈ σ.1, 0 ≤ σ.2 i ∧ σ.2 i ≤ m}

/-- **Definition 3**: `ε`-approximate agreement (`ε = e/m`) among the processes of `S`: outputs in
the range of the inputs, pairwise at distance at most `e`. -/
def aa (S : Finset P) (m e : ℤ) : Task P ℤ ℤ where
  Inp := aaInp S m
  Δ I x := {y | ∀ i ∈ I, InRange I x (y i) ∧ ∀ j ∈ I, abs (y i - y j) ≤ e}

/-- **Definition 4**: the liberal version of `ε`-approximate agreement: if exactly two processes
participate, they only have to output values in the range of the inputs. -/
def libAA (S : Finset P) (m e : ℤ) : Task P ℤ ℤ where
  Inp := aaInp S m
  Δ I x := {y | ∀ i ∈ I, InRange I x (y i) ∧ (I.card ≠ 2 → ∀ j ∈ I, abs (y i - y j) ≤ e)}

/-- Every algorithm for `ε`-approximate agreement solves the liberal version. -/
lemma libAA_easier (S : Finset P) (m e : ℤ) : (libAA S m e).Easier (aa S m e) :=
  Task.Easier.of_subset le_rfl fun _ _ _ _ hy i hi => ⟨(hy i hi).1, fun _ => (hy i hi).2⟩

lemma aa_mono {S : Finset P} {m e e' : ℤ} (h : e ≤ e') : (aa S m e').Easier (aa S m e) :=
  Task.Easier.of_subset le_rfl fun _ _ _ _ hy i hi =>
    ⟨(hy i hi).1, fun j hj => ((hy i hi).2 j hj).trans h⟩

lemma libAA_mono {S : Finset P} {m e e' : ℤ} (h : e ≤ e') :
    (libAA S m e').Easier (libAA S m e) :=
  Task.Easier.of_subset le_rfl fun _ _ _ _ hy i hi =>
    ⟨(hy i hi).1, fun hI j hj => ((hy i hi).2 hI j hj).trans h⟩

/-- Restricting the participants to `S' ⊆ S` makes the task easier. -/
lemma libAA_restrict {S S' : Finset P} (hS : S' ⊆ S) (m e : ℤ) :
    (libAA S' m e).Easier (libAA S m e) :=
  Task.Easier.of_subset (fun _ ⟨h1, h2, h3⟩ => ⟨h1, h2.trans hS, h3⟩) fun _ _ _ _ hy => hy

/-! ### Claim 1 -/

/-- In zero rounds, a process with input `v` decides `v` (it may be running solo). -/
lemma zero_round_dec {A B : Type} {M : Model P A B} {T : Task P ℤ ℤ} {S : Finset P} {m : ℤ}
    (hInp : T.Inp = aaInp S m) (hval : ∀ I x, ∀ y ∈ T.Δ I x, ∀ i ∈ I, InRange I x (y i))
    {alg : Alg P ℤ A B ℤ 0} (h : Solves M T alg) {i : P} (hi : i ∈ S) {v : ℤ} (hv0 : 0 ≤ v)
    (hvm : v ≤ m) : alg.dec i v = v := by
  have hx : ({i}, fun _ => v) ∈ T.Inp := by
    rw [hInp]
    exact ⟨Finset.singleton_nonempty i, Finset.singleton_subset_iff.2 hi, fun _ _ => ⟨hv0, hvm⟩⟩
  obtain ⟨y, hy, hdec⟩ := zero_round_solo h hx
  exact hdec.trans (inRange_singleton.1 (hval _ _ y hy i (Finset.mem_singleton_self i)))

/-- **Claim 1** (`ε`-approximate agreement): for `ε < 1` (i.e. `e < m`) and two processes, there
is no 0-round algorithm (in any model). -/
theorem claim1_aa {A B : Type} (M : Model P A B) {S : Finset P} {p q : P} (hp : p ∈ S)
    (hq : q ∈ S) (hpq : p ≠ q) {m e : ℤ} (hm : 0 ≤ m) (he : e < m) :
    ¬ Solvable M (aa S m e) 0 := by
  rintro ⟨alg, halg⟩
  have hdec := fun {i} (hi : i ∈ S) {v} (h0 : 0 ≤ v) (h1 : v ≤ m) =>
    zero_round_dec rfl (fun I x y hy i hi => (hy i hi).1) halg hi h0 h1
  let x : P → ℤ := fun l => if l = q then m else 0
  obtain ⟨y, hy, hd⟩ := halg {p, q} x
    ⟨Finset.insert_nonempty _ _, by simp [Finset.insert_subset_iff, hp, hq],
      fun i _ => by simp only [x]; split_ifs <;> omega⟩ x Reach.zero
  have h1 := hd p (by simp)
  have h2 := hd q (by simp)
  have h3 := (hy p (by simp)).2 q (by simp)
  rw [hdec hp (by simp [x, hpq]) (by simp [x, hpq, hm])] at h1
  rw [hdec hq (by simp [x, hm]) (by simp [x])] at h2
  simp only [x, hpq, ite_false, ite_true] at h1 h2
  rw [← h1, ← h2, abs_le] at h3
  omega

/-- **Claim 1** (liberal version): for `ε < 1` and three processes, there is no 0-round
algorithm for the liberal version (in any model). -/
theorem claim1_lib {A B : Type} (M : Model P A B) {S : Finset P} {p q r : P} (hp : p ∈ S)
    (hq : q ∈ S) (hr : r ∈ S) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {m e : ℤ} (hm : 0 ≤ m)
    (he : e < m) : ¬ Solvable M (libAA S m e) 0 := by
  rintro ⟨alg, halg⟩
  have hdec := fun {i} (hi : i ∈ S) {v} (h0 : 0 ≤ v) (h1 : v ≤ m) =>
    zero_round_dec rfl (fun I x y hy i hi => (hy i hi).1) halg hi h0 h1
  let x : P → ℤ := fun l => if l = q then m else 0
  have hcard : ({p, q, r} : Finset P).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hpq, hpr]),
      Finset.card_insert_of_notMem (by simp [hqr]), Finset.card_singleton]
  obtain ⟨y, hy, hd⟩ := halg {p, q, r} x
    ⟨Finset.insert_nonempty _ _, by simp [Finset.insert_subset_iff, hp, hq, hr],
      fun i _ => by simp only [x]; split_ifs <;> omega⟩ x Reach.zero
  have h1 := hd p (by simp)
  have h2 := hd q (by simp)
  have h3 := (hy p (by simp)).2 (by omega) q (by simp)
  rw [hdec hp (by simp [x, hpq]) (by simp [x, hpq, hm])] at h1
  rw [hdec hq (by simp [x, hm]) (by simp [x])] at h2
  simp only [x, hpq, ite_false, ite_true] at h1 h2
  rw [← h1, ← h2, abs_le] at h3
  omega

/-! ### The inclusion of Claim 2 -/

/-- **Claim 2**, inclusion `Δ'_ε ⊆ Δ_{3ε}` (the direction used in Corollary 3): the closure of
`ε`-approximate agreement w.r.t. IIS is contained in `3ε`-approximate agreement. (The paper states
it for two processes; the path argument works for any number of processes.) -/
theorem closure_aa_subset {S : Finset P} {m e : ℤ} (I : Finset P) (x : P → ℤ) :
    (closure iis (aa S m e)).Δ I x ⊆ (aa S m (3 * e)).Δ I x := by
  rintro τ ⟨hV, g, hg⟩ i hi
  obtain ⟨y₀, hy₀, hy₀i⟩ := hV i hi
  refine ⟨hy₀i ▸ (hy₀ i hi).1, fun j hj => ?_⟩
  have he : 0 ≤ e := by have := (hy₀ i hi).2 i hi; simp at this; exact this
  by_cases hij : i = j
  · subst hij; simp; omega
  obtain ⟨b, c, ⟨y₁, hy₁, h₁i, h₁j⟩, ⟨y₂, hy₂, h₂j, h₂i⟩, ⟨y₃, hy₃, h₃i, h₃j⟩⟩ :=
    iis_local_path hg hi hj hij
  have e1 := (hy₁ i hi).2 j hj
  have e2 := (hy₂ j hj).2 i hi
  have e3 := (hy₃ i hi).2 j hj
  rw [h₁i, h₁j, abs_le] at e1
  rw [h₂j, h₂i, abs_le] at e2
  rw [h₃i, h₃j, abs_le] at e3
  rw [abs_le]; constructor <;> omega

/-! ### The inclusion of Claims 3, 4, 6 -/

/-- The inclusion `Δ'_ε ⊆ Δ_{2ε}` for the liberal version, for any model in which, for any three
distinct participants `i, j, k`, there are two rounds where `i` (resp. `j`) runs solo first and `k`
gets the same view (Figure 6). -/
theorem libAA_subset_of_local {A B : Type} {M : Model P A B} (hsolo : M.AllowsSolo)
    {b₀ : P → A → B} (hdet : M.SoloDet b₀) {S : Finset P} {m e : ℤ} {I : Finset P}
    {x : P → ℤ} {τ : P → ℤ} (hV : InVertices (libAA S m e) I x τ) {g : Alg P ℤ A B ℤ 1}
    (hg : Solves M (localTask (libAA S m e) I x τ) g)
    (htri : ∀ i ∈ I, ∀ j ∈ I, ∀ k ∈ I, i ≠ j → k ≠ i → k ≠ j →
      ∃ p ∈ M.Pat I (fun l => g.inp 0 l (τ l)), ∃ q ∈ M.Pat I (fun l => g.inp 0 l (τ l)),
        p.sees i = {i} ∧ q.sees j = {j} ∧ p.sees k = q.sees k ∧ p.out k = q.out k) :
    τ ∈ (libAA S m (2 * e)).Δ I x := by
  intro i hi
  obtain ⟨y₀, hy₀, hy₀i⟩ := hV i hi
  refine ⟨hy₀i ▸ (hy₀ i hi).1, fun hI j hj => ?_⟩
  have he : 0 ≤ e := by have := (hy₀ i hi).2 hI i hi; simp at this; exact this
  by_cases hij : i = j
  · subst hij; simp; omega
  have h3 : 3 ≤ I.card := by
    have := one_lt_card_of_ne hi hj hij
    omega
  obtain ⟨k, hk, hki, hkj⟩ := exists_third h3 i j
  obtain ⟨p, hp, q, hq, hpi, hqj, hks, hko⟩ := htri i hi j hj k hk hij hki hkj
  obtain ⟨γ, ⟨y₁, hy₁, h₁i, h₁k⟩, ⟨y₂, hy₂, h₂j, h₂k⟩⟩ :=
    local_triangle hsolo hdet hg hi hj hk hij hp hq hpi hqj hks hko
  have e1 := (hy₁ i hi).2 hI k hk
  have e2 := (hy₂ j hj).2 hI k hk
  rw [h₁i, h₁k, abs_le] at e1
  rw [h₂j, h₂k, abs_le] at e2
  rw [abs_le]; constructor <;> omega

/-- **Claim 3**, inclusion `Δ'_ε ⊆ Δ_{2ε}` (used in Corollary 3 for `n ≥ 3`). -/
theorem claim3_subset {S : Finset P} {m e : ℤ} (I : Finset P) (x : P → ℤ) :
    (closure iis (libAA S m e)).Δ I x ⊆ (libAA S m (2 * e)).Δ I x := by
  rintro τ ⟨hV, g, hg⟩
  refine libAA_subset_of_local iis_allowsSolo iis_soloDet hV hg fun i hi j hj k hk hij hki hkj =>
    ⟨iisPat I (rank3 i j k), iisPat_mem _ _, iisPat I (rank3 j i k), iisPat_mem _ _,
      rank3_solo hi, rank3_solo hj, rank3_third (Ne.symm hki) (Ne.symm hkj), rfl⟩

/-- **Claim 4**, inclusion `Δ'_ε ⊆ Δ_{2ε}` for IIS augmented with test&set. -/
theorem claim4_subset {S : Finset P} {m e : ℤ} (I : Finset P) (x : P → ℤ) :
    (closure iisTS (libAA S m e)).Δ I x ⊆ (libAA S m (2 * e)).Δ I x := by
  rintro τ ⟨hV, g, hg⟩
  refine libAA_subset_of_local iisTS_allowsSolo iisTS_soloDet hV hg
    fun i hi j hj k hk hij hki hkj =>
    ⟨tsPat I (rank3 i j k) i, tsPat_mem hi rank3_zero _, tsPat I (rank3 j i k) j,
      tsPat_mem hj rank3_zero _, rank3_solo hi, rank3_solo hj,
      rank3_third (Ne.symm hki) (Ne.symm hkj), by simp [tsPat, hki, hkj]⟩

end AsyncSpeedup
