import Papers.PODC2017.RegisterEmulationSpace.Lemma1

/-!
# Theorems 1, 5, 6, 7 and (the repaired) Theorem 8

All lower bounds are consequences of Lemma 1 (`Alg.lemma1`) and of one round (`Alg.round_main`).
Common hypotheses: `A` is an `f`-tolerant obstruction-free emulation (`Alg.ObstructionFree δ f Wr`)
of a `k`-register (writers `w 0, …, w (k-1) ∈ Wr`, distinct), safe in sequential runs
(`Alg.SeqSafe v₀ Wr`, implied by WS-Safety), with a reader `rd` different from the writers and a
value `v' ≠ v₀`; `δ : B → S` maps the base registers to the servers.
-/

set_option linter.unusedSectionVars false

namespace Podc.RegisterEmulationSpace

open Finset

/-- Number of base registers stored on server `s`. -/
def load {B S : Type*} [Fintype B] [DecidableEq S] (δ : B → S) (s : S) : ℕ :=
  #(univ.filter fun b => δ b = s)

lemma card_filter_notMem_eq_sum {B S : Type*} [Fintype B] [Fintype S] [DecidableEq S]
    (δ : B → S) (F : Finset S) : #(univ.filter fun b => δ b ∉ F) = ∑ s ∈ Fᶜ, load δ s := by
  rw [card_eq_sum_card_fiberwise (f := δ) (t := Fᶜ)]
  · refine sum_congr rfl fun s hs => ?_
    unfold load
    congr 1
    ext b
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    rintro rfl; simpa using hs
  · intro b hb; simpa using hb

lemma sum_load {B S : Type*} [Fintype B] [Fintype S] [DecidableEq S] (δ : B → S) :
    ∑ s, load δ s = Fintype.card B := by
  rw [← card_univ, card_eq_sum_card_fiberwise (f := δ) (t := univ) (fun _ _ => mem_univ _)]
  rfl

/-- The counting step of Theorem 1: if removing any `f + 1` servers leaves at least `K` registers,
then there are at least `K + ⌈K / (n - (f+1))⌉ (f + 1)` registers. (The paper's proof removes the
whole set `G` of heavy servers in its last step, which Lemma 1 does not allow when `|G| > f + 1`;
we remove `f + 1` of them.) -/
lemma load_bound {S : Type*} [Fintype S] [DecidableEq S] (ℓ : S → ℕ) (f K : ℕ)
    (hn : f + 1 ≤ Fintype.card S) (h : ∀ F : Finset S, #F = f + 1 → K ≤ ∑ s ∈ Fᶜ, ℓ s) :
    K + (K ⌈/⌉ (Fintype.card S - (f + 1))) * (f + 1) ≤ ∑ s, ℓ s := by
  set m := Fintype.card S - (f + 1)
  set c := K ⌈/⌉ m
  set G := univ.filter fun s => c ≤ ℓ s
  have hG : f + 1 ≤ #G := by
    by_contra hlt
    push Not at hlt
    obtain ⟨F, hGF, hF⟩ := exists_superset_card_eq (s := G) (n := f + 1) (by omega) hn
    have hK := h F hF
    have hle : ∑ s ∈ Fᶜ, ℓ s ≤ ∑ s ∈ Fᶜ, (c - 1) := by
      refine sum_le_sum fun s hs => ?_
      have : s ∉ G := fun h' => (mem_compl.1 hs) (hGF h')
      simp only [G, mem_filter, mem_univ, true_and, not_le] at this
      omega
    rw [sum_const, card_compl, hF, smul_eq_mul] at hle
    have hc : c = 0 := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · simp [c, hm]
      · have : c ≤ c - 1 := (ceilDiv_le_iff_le_mul hm).2 (by
          exact hK.trans hle)
        omega
    have : G = univ := by
      ext s; simp [G, hc]
    rw [this, card_univ] at hlt
    omega
  obtain ⟨G', hG'G, hG'⟩ := exists_subset_card_eq hG
  rw [← sum_add_sum_compl G' ℓ]
  have h1 : (f + 1) * c ≤ ∑ s ∈ G', ℓ s := by
    rw [← hG', ← smul_eq_mul, ← sum_const]
    refine sum_le_sum fun s hs => ?_
    have := hG'G hs
    simp only [G, mem_filter, mem_univ, true_and] at this
    exact this
  have h2 := h G' hG'
  rw [mul_comm] at h1
  omega

variable {C B V W L S : Type*} [DecidableEq C] [DecidableEq B] [DecidableEq S] [Fintype B]
  [Fintype S]

namespace Alg

variable (A : Alg C B V W L)

lemma cov_card_le {δ : B → S} {F : Finset S} {X : Cfg C B V W L} (h : ∀ b ∈ Cov X, δ b ∉ F) :
    #(Cov X) ≤ ∑ s ∈ Fᶜ, load δ s := by
  rw [← card_filter_notMem_eq_sum]
  exact card_le_card fun b hb => by simpa using h b hb

/-- **Theorem 1** of the paper. An `f`-tolerant obstruction-free WS-Safe `k`-register emulation over
`n = |S|` servers uses at least `k f + ⌈k f / (n - (f + 1))⌉ (f + 1)` base registers.
We assume only `n ≥ f + 1` (the paper: `n ≥ 2f + 1`, `k, f > 0`) and only safety in sequential runs. -/
theorem theorem1 {δ : B → S} {f : ℕ} {Wr : Set C} {v₀ v' : V} (hv' : v' ≠ v₀)
    (hOF : A.ObstructionFree δ f Wr) (hS : A.SeqSafe v₀ Wr)
    {k : ℕ} {w : ℕ → C} (hwW : ∀ j < k, w j ∈ Wr) (hwinj : ∀ i < k, ∀ j < k, w i = w j → i = j)
    {rd : C} (hrd : ∀ j < k, rd ≠ w j) (hn : f + 1 ≤ Fintype.card S) :
    k * f + (k * f ⌈/⌉ (Fintype.card S - (f + 1))) * (f + 1) ≤ Fintype.card B := by
  rw [← sum_load δ]
  refine load_bound (load δ) f (k * f) hn fun F hF => ?_
  obtain ⟨E, -, hE, -⟩ := A.lemma1 hv' hOF hS (F := F) hF.le hwW hwinj hrd
  obtain ⟨-, hcard, hoff⟩ := hE k le_rfl
  exact hcard.trans (cov_card_le hoff)

/-- **Theorem 5** of the paper: an `f`-tolerant obstruction-free WS-Safe register emulation (with at
least one writer and one other client) needs `|S| ≥ 2f + 1` servers. -/
theorem theorem5 {δ : B → S} {f : ℕ} {Wr : Set C} {v₀ v' : V} (hv' : v' ≠ v₀)
    (hOF : A.ObstructionFree δ f Wr) (hS : A.SeqSafe v₀ Wr) {a rd : C} (ha : a ∈ Wr)
    (hrd : rd ≠ a) : 2 * f + 1 ≤ Fintype.card S := by
  obtain ⟨-, -, -, -, -, Q, P, hQ, -, hP, hQP, -⟩ := A.round_main hOF hS (F := ∅) (by simp)
    (E₀ := []) (by simp) (Ls := []) rfl (by simp) (fun _ => rfl) ha hrd rfl (v := v') hv'
  have := card_union_of_disjoint hQP
  have := card_le_univ (Q ∪ P)
  omega

/-- **Theorem 6** of the paper: with `|S| = 2f + 1` servers (`f > 0`), every server stores at
least `k` registers. -/
theorem theorem6 {δ : B → S} {f : ℕ} {Wr : Set C} {v₀ v' : V} (hv' : v' ≠ v₀)
    (hOF : A.ObstructionFree δ f Wr) (hS : A.SeqSafe v₀ Wr)
    {k : ℕ} {w : ℕ → C} (hwW : ∀ j < k, w j ∈ Wr) (hwinj : ∀ i < k, ∀ j < k, w i = w j → i = j)
    {rd : C} (hrd : ∀ j < k, rd ≠ w j) (hf : 0 < f) (hn : Fintype.card S = 2 * f + 1) (s : S) :
    k ≤ load δ s := by
  obtain ⟨F, hFs, hF⟩ := exists_subset_card_eq (s := univ.erase s) (n := f + 1)
    (by rw [card_erase_of_mem (mem_univ _), card_univ]; omega)
  have hsF : s ∉ F := fun h => by simpa using hFs h
  obtain ⟨E, -, -, hchain⟩ := A.lemma1 hv' hOF hS (F := F) hF.le hwW hwinj hrd
  -- every round covers a new register on `s`
  have hnew : ∀ i < k, ∃ b ∈ Cov (A.run (E (i + 1))) \ Cov (A.run (E i)), δ b = s := by
    intro i hi
    obtain ⟨-, -, Q, hQ, hQF, hQs⟩ := hchain i hi
    have hQc : Q = Fᶜ := by
      refine eq_of_subset_of_card_le (fun t ht => mem_compl.2 fun h' =>
        disjoint_left.1 hQF ht h') ?_
      rw [card_compl, hF, hQ]; omega
    exact hQs s (by rw [hQc]; exact mem_compl.2 hsF)
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · rw [hk0]; exact Nat.zero_le _
  have : Nonempty B := ⟨(hnew 0 hk0).choose⟩
  choose! bs hbs hbδ using hnew
  have hmono : ∀ i j, i ≤ j → j ≤ k → Cov (A.run (E i)) ⊆ Cov (A.run (E j)) := by
    intro i j hij hjk
    induction j, hij using Nat.le_induction with
    | base => exact subset_rfl
    | succ j hij ih => exact (ih (by omega)).trans (hchain j (by omega)).2.1
  have hinj : ∀ i < k, ∀ j < k, bs i = bs j → i = j := by
    intro i hi j hj he
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h1 := (mem_sdiff.1 (hbs i hi)).1
      have h2 := (mem_sdiff.1 (hbs j hj)).2
      exact h2 (he ▸ hmono (i + 1) j h hj.le h1)
    · have h1 := (mem_sdiff.1 (hbs j hj)).1
      have h2 := (mem_sdiff.1 (hbs i hi)).2
      exact h2 (he ▸ hmono (j + 1) i h hi.le h1)
  have : (range k).image bs ⊆ univ.filter fun b => δ b = s := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hb
    simpa using hbδ i (mem_range.1 hi)
  have hcard := card_le_card this
  rw [card_image_of_injOn (fun i hi j hj he => hinj i (mem_range.1 hi) j (mem_range.1 hj) he),
    card_range] at hcard
  exact hcard

/-- **Theorem 7** of the paper: if every server stores at most `m` registers, then
`|S| ≥ ⌈k f / m⌉ + f + 1`. The paper assumes `|S| > 2f + 1`; this is not needed. -/
theorem theorem7 {δ : B → S} {f : ℕ} {Wr : Set C} {v₀ v' : V} (hv' : v' ≠ v₀)
    (hOF : A.ObstructionFree δ f Wr) (hS : A.SeqSafe v₀ Wr)
    {k : ℕ} {w : ℕ → C} (hwW : ∀ j < k, w j ∈ Wr) (hwinj : ∀ i < k, ∀ j < k, w i = w j → i = j)
    {rd : C} (hrd : ∀ j < k, rd ≠ w j) (hk : 0 < k) (hf : 0 < f) {m : ℕ}
    (hm : ∀ s, load δ s ≤ m) :
    k * f ⌈/⌉ m + f + 1 ≤ Fintype.card S := by
  by_cases hn : f + 1 ≤ Fintype.card S
  · obtain ⟨F, -, hF⟩ := exists_subset_card_eq (s := (univ : Finset S)) (n := f + 1)
      (by rwa [card_univ])
    obtain ⟨E, -, hE, -⟩ := A.lemma1 hv' hOF hS (F := F) hF.le hwW hwinj hrd
    obtain ⟨-, hcard, hoff⟩ := hE k le_rfl
    have h1 := hcard.trans (cov_card_le hoff)
    have h2 : ∑ s ∈ Fᶜ, load δ s ≤ #Fᶜ * m := by
      rw [← smul_eq_mul, ← sum_const]; exact sum_le_sum fun s _ => hm s
    rw [card_compl, hF] at h2
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · simp [hm0]; omega
    · have : k * f ⌈/⌉ m ≤ Fintype.card S - (f + 1) :=
        (ceilDiv_le_iff_le_mul hm0).2 (by rw [mul_comm m]; exact h1.trans h2)
      omega
  · -- fewer than `f + 1` servers: take `F = S`, then nothing can be covered
    push Not at hn
    obtain ⟨E, -, hE, -⟩ := A.lemma1 hv' hOF hS (F := univ) (by rw [card_univ]; omega) hwW hwinj
      hrd
    obtain ⟨-, hcard, hoff⟩ := hE k le_rfl
    have : Cov (A.run (E k)) = ∅ := eq_empty_of_forall_notMem fun b hb => hoff b hb (mem_univ _)
    rw [this, card_empty] at hcard
    have := Nat.mul_pos hk hf
    omega

/-- **Theorem 8, repaired.** The resource complexity cannot be bounded by a function of the point
contention that does not depend on the number `k` of writers: for every `M` there is `k` such that
every `f`-tolerant (`f > 0`) obstruction-free WS-Safe `k`-register emulation has a *sequential* run
(point contention `1`) in which more than `M` base registers are in use (covered by pending
writes). As stated in the paper (with `M` allowed to depend on the algorithm, i.e. on `k`) the
theorem is false: every algorithm with finitely many registers is adaptive with a constant `M`. -/
theorem theorem8 {δ : B → S} {f : ℕ} (hf : 0 < f) {Wr : Set C} {v₀ v' : V} (hv' : v' ≠ v₀)
    (hOF : A.ObstructionFree δ f Wr) (hS : A.SeqSafe v₀ Wr) (M : ℕ)
    {w : ℕ → C} (hwW : ∀ j < M + 1, w j ∈ Wr)
    (hwinj : ∀ i < M + 1, ∀ j < M + 1, w i = w j → i = j)
    {rd : C} (hrd : ∀ j < M + 1, rd ≠ w j) :
    ∃ E : List (Ev C V), (∃ Ls, (A.run E).hist = seqHist Ls) ∧ M < #(Cov (A.run E)) := by
  obtain ⟨E, -, hE, -⟩ := A.lemma1 hv' hOF hS (F := ∅) (by simp) hwW hwinj hrd
  obtain ⟨⟨Ls, hL, -⟩, hcard, -⟩ := hE (M + 1) le_rfl
  refine ⟨E (M + 1), ⟨Ls, hL⟩, ?_⟩
  have : M + 1 ≤ (M + 1) * f := Nat.le_mul_of_pos_right _ hf
  omega

end Alg

end Podc.RegisterEmulationSpace
