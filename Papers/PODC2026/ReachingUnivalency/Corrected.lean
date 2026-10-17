import Papers.PODC2026.ReachingUnivalency.RPK

/-!
# Reaching Univalency — a corrected Lemma 6

With the paper's step-1 threshold `k(2/3 - ε/2)`, two correct processors whose samples are
accurate can respond with *different* values in step 1 as soon as samples deviate at all and `f`
is close to `n(1/3 - ε)` (see `Counterexample.lean`). Raising the threshold to `k(2/3 - ε/4)`
restores "time-slot 1 agreement" among accurately sampling processors, and the paper's argument
then goes through, provided samples are accurate also on sets containing the Byzantine
processors (the paper's notion of a bad sampling choice only looks at correct processors).

`lemma6_corrected`: let `δ ≤ ε/8`, and let `B` be a set of processors such that every correct
processor outside `B` samples `δ`-accurately the (at most 20) sets that matter in the execution
(`GoodRound`). If `|B| < |C r| ε` for both committees and `|B| ≤ n(ε - δ)`, then one level of
ε-RPK with step-1 threshold `2/3 - ε/4` achieves ε-BA, the exceptional set being `B`.
-/

namespace ReachingUnivalency.RPK

open Finset

variable {n k : ℕ}

/-- `smp` is `δ`-accurate on `S` (relative to the response set `R`). -/
def Acc (δ : ℚ) (smp : Fin k → Fin n) (R S : Finset (Fin n)) : Prop := |dev smp R S| < δ

section counting

variable {F : Finset (Fin n)} {smp : Fin k → Fin n} {byz ans : Fin n → Option Bool}

lemma cnt_le_card_union (b : Bool) :
    cnt F smp byz ans b ≤ (univ.filter fun j => smp j ∈ corr F ans b ∪ F).card := by
  unfold cnt
  refine card_le_card fun j hj => ?_
  simp only [mem_filter, mem_univ, true_and, corr, mem_union] at hj ⊢
  unfold heard at hj
  by_cases h : smp j ∈ F
  · exact Or.inr h
  · simp only [h, ↓reduceIte] at hj; exact Or.inl ⟨h, hj⟩

lemma card_le_cnt (b : Bool) :
    (univ.filter fun j => smp j ∈ corr F ans b).card ≤ cnt F smp byz ans b := by
  unfold cnt
  refine card_le_card fun j hj => ?_
  simp only [mem_filter, mem_univ, true_and, corr] at hj ⊢
  unfold heard
  simp only [hj.1, ↓reduceIte]; exact hj.2

lemma cnt_add_cnt_le : cnt F smp byz ans true + cnt F smp byz ans false ≤ k := by
  unfold cnt
  rw [← card_union_of_disjoint]
  · exact (card_le_univ _).trans (by simp)
  · rw [disjoint_filter]; intro j _ h1 h2; rw [h1] at h2; simp at h2

lemma corr_disjoint (ans : Fin n → Option Bool) (b : Bool) : Disjoint (corr F ans b) F := by
  rw [disjoint_left]; intro q hq; exact (mem_filter.mp hq).2.1

lemma card_corr_union (ans : Fin n → Option Bool) (b : Bool) :
    (corr F ans b ∪ F).card = (corr F ans b).card + F.card :=
  card_union_of_disjoint (corr_disjoint ans b)

lemma card_corr_add_le (ans : Fin n → Option Bool) :
    (corr F ans true).card + (corr F ans false).card + F.card ≤ n := by
  rw [← card_union_of_disjoint, ← card_union_of_disjoint]
  · exact (card_le_univ _).trans (by simp)
  · rw [disjoint_union_left]; exact ⟨corr_disjoint ans true, corr_disjoint ans false⟩
  · unfold corr; rw [disjoint_filter]; intro q _ h1 h2; rw [h1.2] at h2; simp at h2

lemma card_corr_vals (vals : Fin n → Bool) :
    (corr F (fun q => some (vals q)) true).card + (corr F (fun q => some (vals q)) false).card +
      F.card = n := by
  rw [← card_union_of_disjoint, ← card_union_of_disjoint]
  · rw [show corr F (fun q => some (vals q)) true ∪ corr F (fun q => some (vals q)) false ∪ F =
        univ by
      ext q; simp only [corr, mem_union, mem_filter, mem_univ, true_and, Option.some.injEq,
        iff_true]
      by_cases hq : q ∈ F
      · exact Or.inr hq
      · cases h : vals q <;> simp [hq]]
    simp
  · rw [disjoint_union_left]
    exact ⟨corr_disjoint _ true, corr_disjoint _ false⟩
  · unfold corr; rw [disjoint_filter]; intro q _ h1 h2; rw [h1.2] at h2; simp at h2

end counting

section accuracy

variable {δ : ℚ} {smp : Fin k → Fin n} {R S : Finset (Fin n)}

lemma Acc.lt' (hk : 0 < k) (h : Acc δ smp R S) :
    ((univ.filter fun j => smp j ∈ S).card : ℚ) < k * ((S ∩ R).card / R.card + δ) := by
  have h1 := (abs_lt.mp h).2
  unfold dev at h1
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  have e : ((univ.filter fun j => smp j ∈ S).card : ℚ) =
      k * (((univ.filter fun j => smp j ∈ S).card : ℚ) / k) := by field_simp
  rw [e]
  nlinarith

lemma Acc.gt' (hk : 0 < k) (h : Acc δ smp R S) :
    k * ((S ∩ R).card / R.card - δ) < ((univ.filter fun j => smp j ∈ S).card : ℚ) := by
  have h1 := (abs_lt.mp h).1
  unfold dev at h1
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  have e : ((univ.filter fun j => smp j ∈ S).card : ℚ) =
      k * (((univ.filter fun j => smp j ∈ S).card : ℚ) / k) := by field_simp
  rw [e]
  nlinarith

lemma Acc.lt (hk : 0 < k) (h : Acc δ smp univ S) :
    ((univ.filter fun j => smp j ∈ S).card : ℚ) < k * (S.card / n + δ) := by
  simpa using h.lt' hk

lemma Acc.gt (hk : 0 < k) (h : Acc δ smp univ S) :
    k * (S.card / n - δ) < ((univ.filter fun j => smp j ∈ S).card : ℚ) := by
  simpa using h.gt' hk

end accuracy

section steps

variable {T : ℚ} {σ : Sampling n k} {adv : Adversary n} {r : Fin 2} {vals : Fin n → Bool}
  {resp : Fin n → Option Bool} {vg : Fin n → Bool × ℕ} {p : Fin n}

lemma step1_some {b : Bool} (h : step1 T σ adv r vals p = some b) :
    T * k ≤ cnt adv.F (σ.val r p) (adv.byzVal r · p) (fun q => some (vals q)) b := by
  unfold step1 at h
  dsimp only at h
  split_ifs at h with h1 h2 <;> simp only [Option.some.injEq] at h <;> subst h
    <;> assumption

lemma step1_eq {x : Bool}
    (h1 : T * k ≤ cnt adv.F (σ.val r p) (adv.byzVal r · p) (fun q => some (vals q)) x)
    (h2 : (cnt adv.F (σ.val r p) (adv.byzVal r · p) (fun q => some (vals q)) (!x) : ℚ) < T * k) :
    step1 T σ adv r vals p = some x := by
  unfold step1
  dsimp only
  cases x
  · simp only [Bool.not_false] at h2
    simp [not_le.mpr h2, h1]
  · simp [h1]

lemma step2_two {b : Bool} (h : step2 σ adv r vals resp p = (b, 2)) :
    2/3 * (k : ℚ) ≤ cnt adv.F (σ.resp r p) (adv.byzResp r · p) resp b := by
  unfold step2 at h
  dsimp only at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h
  all_goals first | (obtain ⟨rfl, -⟩ := h; assumption) | exact absurd h.2 (by decide)

lemma step2_grade_two (h : (step2 σ adv r vals resp p).2 = 2) :
    2/3 * (k : ℚ) ≤
      cnt adv.F (σ.resp r p) (adv.byzResp r · p) resp (step2 σ adv r vals resp p).1 := by
  rcases hh : step2 σ adv r vals resp p with ⟨b, g⟩
  rw [hh] at h
  simp only at h
  subst h
  exact step2_two hh

/-- If `x` is seen at least `k/3` times and `!x` fewer than `k/3` times, step 2 sets the value to
`x`. -/
lemma step2_fst {x : Bool}
    (h1 : (k : ℚ)/3 ≤ cnt adv.F (σ.resp r p) (adv.byzResp r · p) resp x)
    (h2 : (cnt adv.F (σ.resp r p) (adv.byzResp r · p) resp (!x) : ℚ) < k/3) :
    (step2 σ adv r vals resp p).1 = x := by
  have hk : (0 : ℚ) ≤ k := by positivity
  unfold step2
  dsimp only
  cases x
  · simp only [Bool.not_false] at h2
    have : ¬ 2/3 * (k : ℚ) ≤ cnt adv.F (σ.resp r p) (adv.byzResp r · p) resp true := by
      intro h; linarith
    have h3 : ¬ (k : ℚ)/3 ≤ cnt adv.F (σ.resp r p) (adv.byzResp r · p) resp true := not_le.mpr h2
    split_ifs <;> simp_all
  · simp only [Bool.not_true] at h2
    have h3 : ¬ (k : ℚ)/3 ≤ cnt adv.F (σ.resp r p) (adv.byzResp r · p) resp false := not_le.mpr h2
    have : ¬ 2/3 * (k : ℚ) ≤ cnt adv.F (σ.resp r p) (adv.byzResp r · p) resp false := by
      intro h; linarith
    split_ifs <;> simp_all

/-- If `x` is seen at least `2k/3` times and `!x` fewer than `k/3` times, step 2 gives `(x, 2)`. -/
lemma step2_eq_two {x : Bool}
    (h1 : 2/3 * (k : ℚ) ≤ cnt adv.F (σ.resp r p) (adv.byzResp r · p) resp x)
    (h2 : (cnt adv.F (σ.resp r p) (adv.byzResp r · p) resp (!x) : ℚ) < k/3) :
    step2 σ adv r vals resp p = (x, 2) := by
  have hk : (0 : ℚ) ≤ k := by positivity
  unfold step2
  dsimp only
  cases x
  · simp only [Bool.not_false] at h2
    have : ¬ 2/3 * (k : ℚ) ≤ cnt adv.F (σ.resp r p) (adv.byzResp r · p) resp true := by
      intro h; linarith
    simp [this, h1]
  · simp [h1]

lemma step3_two (h : (vg p).2 = 2) : step3 σ adv r vg p = (vg p).1 := by
  unfold step3; simp [h]

lemma step3_maj (h : (vg p).2 ≠ 2) {v : Bool}
    (hlt : cnt adv.F (σ.comm r p) (adv.byzComm r · p)
        (fun q => some (adv.comm r (fun q => (vg q).1) q)) (!v) <
      cnt adv.F (σ.comm r p) (adv.byzComm r · p)
        (fun q => some (adv.comm r (fun q => (vg q).1) q)) v) :
    step3 σ adv r vg p = v := by
  unfold step3
  simp only [h, ↓reduceIte]
  cases v
  · simp only [Bool.not_false] at hlt
    simp [hlt, not_lt.mpr hlt.le]
  · simp only [Bool.not_true] at hlt
    simp [hlt]

end steps

/-! ### One round -/

/-- The corrected step-1 threshold `2/3 - ε/4` (the paper uses `2/3 - ε/2`). -/
abbrev T1c (ε : ℚ) : ℚ := 2/3 - ε/4

section round

variable (σ : Sampling n k) (adv : Adversary n) (C : Fin 2 → Finset (Fin n)) (ε δ : ℚ)

/-- Correct processors with value `b`. -/
abbrev Vset (vals : Fin n → Bool) (b : Bool) : Finset (Fin n) := corr adv.F (fun q => some (vals q)) b

/-- Correct processors with step-1 response `b`. -/
abbrev Aset (r : Fin 2) (vals : Fin n → Bool) (b : Bool) : Finset (Fin n) :=
  corr adv.F (step1 (T1c ε) σ adv r vals) b

/-- Values and grades after step 2. -/
abbrev VG (r : Fin 2) (vals : Fin n → Bool) : Fin n → Bool × ℕ :=
  step2 σ adv r vals (step1 (T1c ε) σ adv r vals)

/-- Correct processors whose committee output (round `r`) is `b`. -/
abbrev Oset (r : Fin 2) (vals : Fin n → Bool) (b : Bool) : Finset (Fin n) :=
  corr adv.F (fun q => some (adv.comm r (fun q => (VG σ adv ε r vals q).1) q)) b

/-- Processor `p` samples accurately (to within `δ`) the sets that matter in round `r` started
with values `vals`: correct processors with value `b` (with and without the Byzantine ones) in
step 1, correct processors with response `b` (with and without the Byzantine ones) in step 2, and
committee members with output `b` in step 3. -/
def GoodRound (r : Fin 2) (vals : Fin n → Bool) (p : Fin n) : Prop :=
  ∀ b, Acc δ (σ.val r p) univ (Vset adv vals b ∪ adv.F) ∧ Acc δ (σ.val r p) univ (Vset adv vals b) ∧
    Acc δ (σ.resp r p) univ (Aset σ adv ε r vals b ∪ adv.F) ∧
    Acc δ (σ.resp r p) univ (Aset σ adv ε r vals b) ∧
    Acc δ (σ.comm r p) (C r) (Oset σ adv ε r vals b)

/-- The standing hypotheses. -/
structure Hyp (σ : Sampling n k) (adv : Adversary n) (C : Fin 2 → Finset (Fin n)) (ε δ : ℚ)
    (B : Finset (Fin n)) : Prop where
  hk : 0 < k
  hn : 0 < n
  hε : 0 < ε
  hε3 : ε < 1/3
  hδ0 : 0 ≤ δ
  hδ : δ ≤ ε/8
  hF : ((adv.F.card : ℕ) : ℚ) < n * (1/3 - ε)
  hsplit : CommitteeSplit C
  hB : ∀ r, ((B.card : ℕ) : ℚ) < (C r).card * ε
  hBn : ((B.card : ℕ) : ℚ) ≤ n * (ε - δ)
  hcomm : CommOK adv ε C

lemma frac_le {a b : ℕ} (h : a ≤ b) : (a : ℚ) / k ≤ b / k :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

lemma card_div (S : Finset (Fin n)) (F : Finset (Fin n)) (h : Disjoint S F) :
    ((S ∪ F).card : ℚ) / n = S.card / n + F.card / n := by
  rw [card_union_of_disjoint h]; push_cast; ring

lemma dev_univ (smp : Fin k → Fin n) (S : Finset (Fin n)) :
    dev smp univ S = ((univ.filter fun j => smp j ∈ S).card : ℚ) / k - S.card / n := by
  simp [dev]

lemma Acc.frac_lt {smp : Fin k → Fin n} {S : Finset (Fin n)} (h : Acc δ smp univ S) :
    ((univ.filter fun j => smp j ∈ S).card : ℚ) / k < S.card / n + δ := by
  have := (abs_lt.mp h).2; rw [dev_univ] at this; linarith

lemma Acc.frac_gt {smp : Fin k → Fin n} {S : Finset (Fin n)} (h : Acc δ smp univ S) :
    (S.card : ℚ) / n - δ < ((univ.filter fun j => smp j ∈ S).card : ℚ) / k := by
  have := (abs_lt.mp h).1; rw [dev_univ] at this; linarith

variable {σ adv C ε δ} {B : Finset (Fin n)} (H : Hyp σ adv C ε δ B) {r : Fin 2}
  {vals : Fin n → Bool}
include H

lemma Hyp.fn : (adv.F.card : ℚ) / n < 1/3 - ε := by
  have hn : (0 : ℚ) < n := by exact_mod_cast H.hn
  rw [div_lt_iff₀ hn]; linarith [H.hF]

lemma Hyp.Bn : (B.card : ℚ) / n ≤ ε - δ := by
  have hn : (0 : ℚ) < n := by exact_mod_cast H.hn
  rw [div_le_iff₀ hn]; linarith [H.hBn]

lemma Hyp.le_frac {T : ℚ} {c : ℕ} (h : T * k ≤ c) : T ≤ (c : ℚ) / k := by
  have hk : (0 : ℚ) < k := by exact_mod_cast H.hk
  rwa [le_div_iff₀ hk]

lemma Hyp.mul_le_of_frac {T : ℚ} {c : ℕ} (h : T ≤ (c : ℚ) / k) : T * k ≤ c := by
  have hk : (0 : ℚ) < k := by exact_mod_cast H.hk
  rwa [le_div_iff₀ hk] at h

lemma Hyp.lt_of_frac {T : ℚ} {c : ℕ} (h : (c : ℚ) / k < T) : (c : ℚ) < T * k := by
  have hk : (0 : ℚ) < k := by exact_mod_cast H.hk
  rwa [div_lt_iff₀ hk] at h

omit H in
/-- Upper bound on what a good processor hears in step 1. -/
lemma s1_upper {p : Fin n} (hp : GoodRound σ adv C ε δ r vals p) (b : Bool) :
    (cnt adv.F (σ.val r p) (adv.byzVal r · p) (fun q => some (vals q)) b : ℚ) / k <
      (Vset adv vals b).card / n + adv.F.card / n + δ := by
  have h1 := frac_le (k := k) (cnt_le_card_union (F := adv.F) (smp := σ.val r p)
    (byz := (adv.byzVal r · p)) (ans := fun q => some (vals q)) b)
  have h2 := (hp b).1.frac_lt
  rw [card_div _ _ (corr_disjoint _ b)] at h2
  linarith

omit H in
lemma s1_lower {p : Fin n} (hp : GoodRound σ adv C ε δ r vals p) (b : Bool) :
    ((Vset adv vals b).card : ℚ) / n - δ <
      (cnt adv.F (σ.val r p) (adv.byzVal r · p) (fun q => some (vals q)) b : ℚ) / k := by
  have h1 := frac_le (k := k) (card_le_cnt (F := adv.F) (smp := σ.val r p)
    (byz := (adv.byzVal r · p)) (ans := fun q => some (vals q)) b)
  have h2 := (hp b).2.1.frac_gt
  linarith

lemma frac_vals : ((Vset adv vals true).card : ℚ) / n + (Vset adv vals false).card / n +
    adv.F.card / n = 1 := by
  have hn : (0 : ℚ) < n := by exact_mod_cast H.hn
  have := card_corr_vals (F := adv.F) vals
  rw [← add_div, ← add_div, div_eq_one_iff_eq (ne_of_gt hn)]
  exact_mod_cast this

/-- **Time-slot-1 agreement** among good processors (this is where the raised threshold is
needed). -/
lemma s1_agree {p p' : Fin n} (hp : GoodRound σ adv C ε δ r vals p)
    (hp' : GoodRound σ adv C ε δ r vals p') {b : Bool}
    (h : step1 (T1c ε) σ adv r vals p = some b) (h' : step1 (T1c ε) σ adv r vals p' = some (!b)) :
    False := by
  have e1 := H.le_frac (step1_some h)
  have e2 := H.le_frac (step1_some h')
  have u1 := s1_upper hp b
  have u2 := s1_upper hp' (!b)
  have hv := frac_vals H (vals := vals)
  have := H.fn; have := H.hδ; have := H.hε
  simp only [T1c] at e1 e2
  cases b <;> simp only [Bool.not_false, Bool.not_true] at u2 e2 <;> linarith

/-- Step-1 validity: if more than `2n/3` correct processors have value `x`, every good processor
responds `x`. -/
lemma s1_valid {x : Bool} (hx : 2/3 < ((Vset adv vals x).card : ℚ) / n) {p : Fin n}
    (hp : GoodRound σ adv C ε δ r vals p) : step1 (T1c ε) σ adv r vals p = some x := by
  have l := s1_lower hp x
  have u := s1_upper hp (!x)
  have hv := frac_vals H (vals := vals)
  have := H.fn; have := H.hδ; have := H.hε; have := H.hε3
  refine step1_eq (H.mul_le_of_frac ?_) (H.lt_of_frac ?_)
  · simp only [T1c]; linarith
  · simp only [T1c]
    cases x <;> simp only [Bool.not_false, Bool.not_true] at u ⊢ <;> linarith

lemma Hyp.third_le {c : ℕ} (h : 1/3 ≤ (c : ℚ) / k) : (k : ℚ) / 3 ≤ c := by
  have := H.mul_le_of_frac h; linarith

lemma Hyp.lt_third {c : ℕ} (h : (c : ℚ) / k < 1/3) : (c : ℚ) < k / 3 := by
  have := H.lt_of_frac h; linarith

lemma Hyp.frac_add {c d : ℕ} (h : c + d ≤ k) : (c : ℚ) / k + d / k ≤ 1 := by
  have hk : (0 : ℚ) < k := by exact_mod_cast H.hk
  rw [← add_div, div_le_one hk]; exact_mod_cast h

omit H in
lemma s2_upper {p : Fin n} (hp : GoodRound σ adv C ε δ r vals p) (b : Bool) :
    (cnt adv.F (σ.resp r p) (adv.byzResp r · p) (step1 (T1c ε) σ adv r vals) b : ℚ) / k <
      (Aset σ adv ε r vals b).card / n + adv.F.card / n + δ := by
  have h1 := frac_le (k := k) (cnt_le_card_union (F := adv.F) (smp := σ.resp r p)
    (byz := (adv.byzResp r · p)) (ans := step1 (T1c ε) σ adv r vals) b)
  have h2 := (hp b).2.2.1.frac_lt
  rw [card_div _ _ (corr_disjoint _ b)] at h2
  linarith

omit H in
lemma s2_lower {p : Fin n} (hp : GoodRound σ adv C ε δ r vals p) (b : Bool) :
    ((Aset σ adv ε r vals b).card : ℚ) / n - δ <
      (cnt adv.F (σ.resp r p) (adv.byzResp r · p) (step1 (T1c ε) σ adv r vals) b : ℚ) / k := by
  have h1 := frac_le (k := k) (card_le_cnt (F := adv.F) (smp := σ.resp r p)
    (byz := (adv.byzResp r · p)) (ans := step1 (T1c ε) σ adv r vals) b)
  have h2 := (hp b).2.2.2.1.frac_gt
  linarith

/-- **Knowledge of agreement**: if a good processor gets grade 2 with value `b`, every good
processor has value `b` after step 2. -/
lemma s2_know (hgood : ∀ p, p ∉ adv.F → p ∉ B → GoodRound σ adv C ε δ r vals p)
    {p q : Fin n} (hpF : p ∉ adv.F) (hpB : p ∉ B) (hqF : q ∉ adv.F) (hqB : q ∉ B)
    (h2 : (VG σ adv ε r vals p).2 = 2) :
    (VG σ adv ε r vals q).1 = (VG σ adv ε r vals p).1 := by
  set b := (VG σ adv ε r vals p).1
  have hn : (0 : ℚ) < n := by exact_mod_cast H.hn
  have e := H.le_frac (step2_grade_two h2)
  have u := s2_upper (hgood p hpF hpB) b
  have := H.fn; have := H.Bn; have := H.hδ; have := H.hδ0; have := H.hε
  -- some good processor responded `b` in step 1
  have hAb : ¬ (Aset σ adv ε r vals b ⊆ B) := by
    intro hsub
    have : ((Aset σ adv ε r vals b).card : ℚ) / n ≤ B.card / n :=
      div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hsub) hn.le
    linarith
  obtain ⟨g, hgA, hgB⟩ := not_subset.mp hAb
  have hgF : g ∉ adv.F := (mem_filter.mp hgA).2.1
  have hgresp : step1 (T1c ε) σ adv r vals g = some b := (mem_filter.mp hgA).2.2
  -- hence no good processor responded `!b`
  have hsub : Aset σ adv ε r vals (!b) ⊆ B := by
    intro x hx
    by_contra hxB
    exact s1_agree H (hgood g hgF hgB) (hgood x (mem_filter.mp hx).2.1 hxB) hgresp
      (mem_filter.mp hx).2.2
  have hAnb : ((Aset σ adv ε r vals (!b)).card : ℚ) / n ≤ B.card / n :=
    div_le_div_of_nonneg_right (by exact_mod_cast card_le_card hsub) hn.le
  have l := s2_lower (hgood q hqF hqB) b
  have u' := s2_upper (hgood q hqF hqB) (!b)
  exact step2_fst (H.third_le (by linarith)) (H.lt_third (by linarith))

/-- **Validity⁺**: if every good processor responded `x` in step 1, every good processor gets
`x` with grade 2. -/
lemma s2_valid (hgood : ∀ p, p ∉ adv.F → p ∉ B → GoodRound σ adv C ε δ r vals p) {x : Bool}
    (hall : ∀ p, p ∉ adv.F → p ∉ B → step1 (T1c ε) σ adv r vals p = some x)
    {q : Fin n} (hqF : q ∉ adv.F) (hqB : q ∉ B) : VG σ adv ε r vals q = (x, 2) := by
  have hn : (0 : ℚ) < n := by exact_mod_cast H.hn
  have hsub : (univ \ adv.F) \ B ⊆ Aset σ adv ε r vals x := by
    intro p hp
    simp only [mem_sdiff, mem_univ, true_and] at hp
    exact mem_filter.mpr ⟨mem_univ _, hp.1, hall p hp.1 hp.2⟩
  have h1 : n ≤ ((univ \ adv.F) \ B).card + B.card + adv.F.card := by
    have a := card_le_card_sdiff_add_card (s := (univ : Finset (Fin n))) (t := adv.F)
    have b := card_le_card_sdiff_add_card (s := univ \ adv.F) (t := B)
    simp only [card_univ, Fintype.card_fin] at a
    omega
  have h2 : 1 ≤ ((Aset σ adv ε r vals x).card : ℚ) / n + B.card / n + adv.F.card / n := by
    rw [← add_div, ← add_div, le_div_iff₀ hn, one_mul]
    have := card_le_card hsub
    have : (n : ℚ) ≤ ((univ \ adv.F) \ B).card + B.card + adv.F.card := by exact_mod_cast h1
    have : (((univ \ adv.F) \ B).card : ℚ) ≤ (Aset σ adv ε r vals x).card := by
      exact_mod_cast card_le_card hsub
    linarith
  have l := s2_lower (hgood q hqF hqB) x
  have := H.fn; have := H.Bn; have := H.hδ; have := H.hε
  have hsum := H.frac_add (cnt_add_cnt_le (F := adv.F) (smp := σ.resp r q)
    (byz := (adv.byzResp r · q)) (ans := step1 (T1c ε) σ adv r vals))
  refine step2_eq_two (H.mul_le_of_frac (by linarith)) (H.lt_third ?_)
  cases x <;> simp only [Bool.not_false, Bool.not_true] at l ⊢ <;> linarith

/-- In a round whose committee is within its fault bound, all good processors that do not hold
grade 2 adopt the committee value `v`. -/
lemma s3_maj (hgood : ∀ p, p ∉ adv.F → p ∉ B → GoodRound σ adv C ε δ r vals p)
    (hin : (((C r ∩ adv.F).card : ℕ) : ℚ) < (C r).card * (1/3 - ε)) :
    ∃ v : Bool,
      (∀ x, ((((C r \ adv.F).filter fun p => (VG σ adv ε r vals p).1 ≠ x).card : ℕ) : ℚ) <
        (C r).card * ε → v = x) ∧
      ∀ p, p ∉ adv.F → p ∉ B → (VG σ adv ε r vals p).2 ≠ 2 →
        step3 σ adv r (VG σ adv ε r vals) p = v := by
  obtain ⟨X, v, hX, hXc, hagr, hval⟩ := H.hcomm r (fun q => (VG σ adv ε r vals q).1) hin
  refine ⟨v, hval, fun p hpF hpB hp2 => step3_maj hp2 ?_⟩
  have hC : (0 : ℚ) < (C r).card := by
    by_contra h
    push Not at h
    have h0 : ((C r).card : ℚ) = 0 := le_antisymm h (by positivity)
    have : (0 : ℚ) ≤ (C r ∩ adv.F).card := by positivity
    rw [h0, zero_mul] at hin; linarith
  set O := Oset σ adv ε r vals v
  have hsub : (C r \ adv.F) \ X ⊆ O ∩ C r := by
    intro q hq
    simp only [mem_sdiff] at hq
    refine mem_inter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hq.1.2, ?_⟩, hq.1.1⟩
    show some (adv.comm r (fun q => (VG σ adv ε r vals q).1) q) = some v
    rw [hagr q (mem_sdiff.mpr hq.1) hq.2]
  have hcard : (C r).card ≤ ((C r \ adv.F) \ X).card + X.card + (C r ∩ adv.F).card := by
    have := card_le_card_sdiff_add_card (s := C r \ adv.F) (t := X)
    have := card_sdiff_inter (C r) adv.F
    omega
  have hfrac : 2/3 < ((O ∩ C r).card : ℚ) / (C r).card := by
    rw [lt_div_iff₀ hC]
    have : ((C r).card : ℚ) ≤ ((C r \ adv.F) \ X).card + X.card + (C r ∩ adv.F).card := by
      exact_mod_cast hcard
    have : (((C r \ adv.F) \ X).card : ℚ) ≤ (O ∩ C r).card := by exact_mod_cast card_le_card hsub
    nlinarith
  have hacc := ((hgood p hpF hpB) v).2.2.2.2
  have g := (abs_lt.mp hacc).1
  unfold dev at g
  have h1 := frac_le (k := k) (card_le_cnt (F := adv.F) (smp := σ.comm r p)
    (byz := (adv.byzComm r · p)) (ans := fun q => some (adv.comm r (fun q => (VG σ adv ε r vals q).1) q)) v)
  have hsum := H.frac_add (cnt_add_cnt_le (F := adv.F) (smp := σ.comm r p)
    (byz := (adv.byzComm r · p))
    (ans := fun q => some (adv.comm r (fun q => (VG σ adv ε r vals q).1) q)))
  have := H.hδ; have := H.hε; have := H.hε3
  have key : (cnt adv.F (σ.comm r p) (adv.byzComm r · p)
      (fun q => some (adv.comm r (fun q => (VG σ adv ε r vals q).1) q)) (!v) : ℚ) / k <
      (cnt adv.F (σ.comm r p) (adv.byzComm r · p)
      (fun q => some (adv.comm r (fun q => (VG σ adv ε r vals q).1) q)) v : ℚ) / k := by
    cases v <;> simp only [Bool.not_false, Bool.not_true] at hsum ⊢ <;> linarith
  have hk : (0 : ℚ) < k := by exact_mod_cast H.hk
  rw [div_lt_div_iff_of_pos_right hk] at key
  exact_mod_cast key

/-- **Validity of a round**: if fewer than `nε` correct processors start with a value other than
`x`, every good processor ends the round with `x`. -/
lemma round_valid (hgood : ∀ p, p ∉ adv.F → p ∉ B → GoodRound σ adv C ε δ r vals p) {x : Bool}
    (hx : (((univ.filter fun q => q ∉ adv.F ∧ vals q ≠ x).card : ℕ) : ℚ) < n * ε)
    {p : Fin n} (hpF : p ∉ adv.F) (hpB : p ∉ B) : round (T1c ε) σ adv r vals p = x := by
  have hn : (0 : ℚ) < n := by exact_mod_cast H.hn
  have hV : Vset adv vals (!x) = univ.filter fun q => q ∉ adv.F ∧ vals q ≠ x := by
    ext q; cases x <;> simp [corr]
  have hv := frac_vals H (vals := vals)
  have hx' : ((Vset adv vals (!x)).card : ℚ) / n < ε := by
    rw [hV, div_lt_iff₀ hn]; linarith
  have := H.fn
  have h2 : 2/3 < ((Vset adv vals x).card : ℚ) / n := by
    cases x <;> simp only [Bool.not_false, Bool.not_true] at hx' <;> linarith
  have hall := fun q hqF hqB => s1_valid H h2 (hgood q hqF hqB)
  have hvg := s2_valid H hgood hall hpF hpB
  show step3 σ adv r (VG σ adv ε r vals) p = x
  rw [step3_two (by rw [hvg]), hvg]

/-- **Agreement after a round with a sufficiently honest committee.** -/
lemma round_agree (hgood : ∀ p, p ∉ adv.F → p ∉ B → GoodRound σ adv C ε δ r vals p)
    (hin : (((C r ∩ adv.F).card : ℕ) : ℚ) < (C r).card * (1/3 - ε)) :
    ∃ c, ∀ p, p ∉ adv.F → p ∉ B → round (T1c ε) σ adv r vals p = c := by
  obtain ⟨v, hval, hmaj⟩ := s3_maj H hgood hin
  by_cases hA : ∃ g, g ∉ adv.F ∧ g ∉ B ∧ (VG σ adv ε r vals g).2 = 2
  · obtain ⟨g, hgF, hgB, hg2⟩ := hA
    set b := (VG σ adv ε r vals g).1
    have hall : ∀ q, q ∉ adv.F → q ∉ B → (VG σ adv ε r vals q).1 = b :=
      fun q hqF hqB => s2_know H hgood hgF hgB hqF hqB hg2
    have hvb : v = b := by
      apply hval b
      refine lt_of_le_of_lt ?_ (H.hB r)
      refine Nat.cast_le.mpr (card_le_card fun q hq => ?_)
      simp only [mem_filter, mem_sdiff] at hq
      by_contra hqB
      exact hq.2 (hall q hq.1.2 hqB)
    refine ⟨b, fun q hqF hqB => ?_⟩
    show step3 σ adv r (VG σ adv ε r vals) q = b
    by_cases hq2 : (VG σ adv ε r vals q).2 = 2
    · rw [step3_two hq2, hall q hqF hqB]
    · rw [hmaj q hqF hqB hq2, hvb]
  · push Not at hA
    exact ⟨v, fun q hqF hqB => hmaj q hqF hqB (hA q hqF hqB)⟩

end round

/-- **Lemma 6, corrected.** One level of ε-RPK with step-1 threshold `k(2/3 - ε/4)` achieves ε-BA
(with exceptional set `B`) whenever every correct processor outside `B` samples accurately the
sets that matter (`GoodRound`, accuracy `δ ≤ ε/8`), `|B| < |C r| ε` for both committees and
`|B| ≤ n(ε - δ)`; the committee instances only need to solve ε-BA when within their fault
bound (`Hyp`). -/
theorem lemma6_corrected {σ : Sampling n k} {adv : Adversary n} {C : Fin 2 → Finset (Fin n)}
    {ε δ : ℚ} {B : Finset (Fin n)} (H : Hyp σ adv C ε δ B) (inp : Fin n → Bool)
    (hgood : ∀ r p, p ∉ adv.F → p ∉ B →
      GoodRound σ adv C ε δ r (valsAt (T1c ε) σ adv inp r) p) :
    EpsBA ε adv.F inp (output (T1c ε) σ adv inp) := by
  have hn : (0 : ℚ) < n := by exact_mod_cast H.hn
  have hF := H.hF
  have hε := H.hε
  have hBn : (B.card : ℚ) < n * ε := by
    refine lt_of_lt_of_le (H.hB 0) (mul_le_mul_of_nonneg_right ?_ hε.le)
    have := card_le_univ (C 0); simp only [Fintype.card_fin] at this; exact_mod_cast this
  have hout : output (T1c ε) σ adv inp =
      round (T1c ε) σ adv 1 (valsAt (T1c ε) σ adv inp 1) := rfl
  -- if all good processors agree on `c` before round 1, they all output `c`
  have persist : ∀ c, (∀ p, p ∉ adv.F → p ∉ B → valsAt (T1c ε) σ adv inp 1 p = c) →
      ∀ p, p ∉ adv.F → p ∉ B → output (T1c ε) σ adv inp p = c := by
    intro c hc p hpF hpB
    rw [hout]
    refine round_valid H (hgood 1) ?_ hpF hpB
    refine lt_of_le_of_lt (Nat.cast_le.mpr (card_le_card fun q hq => ?_)) hBn
    simp only [mem_filter, mem_univ, true_and] at hq
    by_contra hqB
    exact hq.2 (hc q hq.1 hqB)
  -- some committee is sufficiently honest
  obtain ⟨r, hr⟩ : ∃ r : Fin 2, (((C r ∩ adv.F).card : ℕ) : ℚ) < (C r).card * (1/3 - ε) := by
    by_contra h
    push Not at h
    obtain ⟨hdisj, hunion, -, -⟩ := H.hsplit
    have e1 : (C 0 ∩ adv.F).card + (C 1 ∩ adv.F).card = adv.F.card := by
      rw [← card_union_of_disjoint (disjoint_of_subset_left inter_subset_left
        (disjoint_of_subset_right inter_subset_left hdisj)), ← union_inter_distrib_right,
        hunion, univ_inter]
    have e2 : (C 0).card + (C 1).card = n := by
      rw [← card_union_of_disjoint hdisj, hunion, card_univ, Fintype.card_fin]
    have e1' : ((C 0 ∩ adv.F).card : ℚ) + (C 1 ∩ adv.F).card = adv.F.card := by exact_mod_cast e1
    have e2' : ((C 0).card : ℚ) + (C 1).card = n := by exact_mod_cast e2
    have h0 := h 0
    have h1 := h 1
    nlinarith
  -- agreement among good processors
  obtain ⟨c, hc⟩ : ∃ c, ∀ p, p ∉ adv.F → p ∉ B → output (T1c ε) σ adv inp p = c := by
    fin_cases r
    · obtain ⟨c, hc⟩ := round_agree H (hgood 0) hr
      exact ⟨c, persist c hc⟩
    · obtain ⟨c, hc⟩ := round_agree H (hgood 1) hr
      exact ⟨c, fun p hpF hpB => by rw [hout]; exact hc p hpF hpB⟩
  refine ⟨B \ adv.F, c, fun p hp => ?_, ?_, fun p hp hpX => ?_, fun x hx => ?_⟩
  · simp only [mem_sdiff, mem_univ, true_and] at hp ⊢; exact hp.2
  · simp only [card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (Nat.cast_le.mpr (card_le_card sdiff_subset)) hBn
  · simp only [mem_sdiff, mem_univ, true_and, not_and, not_not] at hp hpX
    exact hc p hp (fun hpB => hp (hpX hpB))
  · -- ε-Validity: round 0 brings all good processors to `x`, round 1 keeps it
    obtain ⟨g, hgF, hgB⟩ : ∃ g, g ∉ adv.F ∧ g ∉ B := by
      by_contra h
      push Not at h
      have hsub : (univ : Finset (Fin n)) ⊆ adv.F ∪ B := fun p _ => by
        by_cases hp : p ∈ adv.F
        · exact mem_union_left _ hp
        · exact mem_union_right _ (h p hp)
      have h1 := (card_le_card hsub).trans (card_union_le adv.F B)
      simp only [card_univ, Fintype.card_fin] at h1
      have : (n : ℚ) ≤ adv.F.card + B.card := by exact_mod_cast h1
      have := H.hε3
      nlinarith
    have hx' : (((univ.filter fun q => q ∉ adv.F ∧ inp q ≠ x).card : ℕ) : ℚ) < n * ε := by
      have : (univ.filter fun q => q ∉ adv.F ∧ inp q ≠ x) =
          ((univ \ adv.F).filter fun p => inp p ≠ x) := by
        ext q
        simp only [mem_filter, mem_sdiff, mem_univ, true_and]
      rw [this]
      simpa using hx
    have h0 : ∀ p, p ∉ adv.F → p ∉ B → valsAt (T1c ε) σ adv inp 1 p = x :=
      fun p hpF hpB => round_valid H (hgood 0) hx' hpF hpB
    rw [← hc g hgF hgB, persist x h0 g hgF hgB]

/-! ### From a sampler property to the exceptional set -/

/-- The sample family `smp` (one list of `k` samples per processor) is `(δ, M)`-good on the response
set `R`: for **every** set `S`, at most `M` processors sample `S` with deviation `≥ δ`. This is the
corrected form of the paper's "not bad in any configuration" (it also covers sets containing
Byzantine processors). -/
def SamplerGood (δ M : ℚ) (smp : Fin n → Fin k → Fin n) (R : Finset (Fin n)) : Prop :=
  ∀ S : Finset (Fin n), (((univ.filter fun p => δ ≤ |dev (smp p) R S|).card : ℕ) : ℚ) ≤ M

/-- All six sample families of a sampling choice are `(δ, M)`-good. -/
def SamplingGood (δ M : ℚ) (σ : Sampling n k) (C : Fin 2 → Finset (Fin n)) : Prop :=
  ∀ r, SamplerGood δ M (σ.val r) univ ∧ SamplerGood δ M (σ.resp r) univ ∧
    SamplerGood δ M (σ.comm r) (C r)

lemma card_union5_le {α : Type*} [DecidableEq α] (a b c d e : Finset α) :
    (a ∪ b ∪ c ∪ d ∪ e).card ≤ a.card + b.card + c.card + d.card + e.card := by
  have h1 := card_union_le (a ∪ b ∪ c ∪ d) e
  have h2 := card_union_le (a ∪ b ∪ c) d
  have h3 := card_union_le (a ∪ b) c
  have h4 := card_union_le a b
  omega

/-- A `(δ, M)`-good sampling choice leaves at most `20 M` processors that are not good in some
round of a given execution. -/
theorem exists_exceptional {σ : Sampling n k} {adv : Adversary n} {C : Fin 2 → Finset (Fin n)}
    {ε δ M : ℚ} (hσ : SamplingGood δ M σ C) (inp : Fin n → Bool) :
    ∃ B : Finset (Fin n), (B.card : ℚ) ≤ 20 * M ∧ ∀ r p, p ∉ adv.F → p ∉ B →
      GoodRound σ adv C ε δ r (valsAt (T1c ε) σ adv inp r) p := by
  classical
  let I : Fin 2 → Bool → Finset (Fin n) := fun r b =>
    let vals := valsAt (T1c ε) σ adv inp r
    (univ.filter fun p => δ ≤ |dev (σ.val r p) univ (Vset adv vals b ∪ adv.F)|) ∪
    (univ.filter fun p => δ ≤ |dev (σ.val r p) univ (Vset adv vals b)|) ∪
    (univ.filter fun p => δ ≤ |dev (σ.resp r p) univ (Aset σ adv ε r vals b ∪ adv.F)|) ∪
    (univ.filter fun p => δ ≤ |dev (σ.resp r p) univ (Aset σ adv ε r vals b)|) ∪
    (univ.filter fun p => δ ≤ |dev (σ.comm r p) (C r) (Oset σ adv ε r vals b)|)
  refine ⟨(univ : Finset (Fin 2 × Bool)).biUnion fun x => I x.1 x.2, ?_, ?_⟩
  · have hI : ∀ r b, ((I r b).card : ℚ) ≤ 5 * M := by
      intro r b
      obtain ⟨h1, h2, h3⟩ := hσ r
      have e : (I r b).card ≤ _ := card_union5_le _ _ _ _ _
      have e' := (Nat.cast_le (α := ℚ)).mpr e
      have := h1 (Vset adv (valsAt (T1c ε) σ adv inp r) b ∪ adv.F)
      have := h1 (Vset adv (valsAt (T1c ε) σ adv inp r) b)
      have := h2 (Aset σ adv ε r (valsAt (T1c ε) σ adv inp r) b ∪ adv.F)
      have := h2 (Aset σ adv ε r (valsAt (T1c ε) σ adv inp r) b)
      have := h3 (Oset σ adv ε r (valsAt (T1c ε) σ adv inp r) b)
      push_cast at e'
      linarith
    have := card_biUnion_le (s := (univ : Finset (Fin 2 × Bool))) (t := fun x => I x.1 x.2)
    have h' : (((univ : Finset (Fin 2 × Bool)).biUnion fun x => I x.1 x.2).card : ℚ) ≤
        ∑ x : Fin 2 × Bool, ((I x.1 x.2).card : ℚ) := by exact_mod_cast this
    refine h'.trans ((sum_le_sum fun x _ => hI x.1 x.2).trans ?_)
    simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
      nsmul_eq_mul]
    norm_num
    linarith
  · intro r p _ hpB b
    have hp : p ∉ I r b := fun h => hpB (mem_biUnion.mpr ⟨(r, b), mem_univ _, h⟩)
    simp only [I, mem_union, mem_filter, mem_univ, true_and, not_or, not_le] at hp
    exact ⟨hp.1.1.1.1, hp.1.1.1.2, hp.1.1.2, hp.1.2, hp.2⟩

/-- **Lemma 6, corrected, sampler form.** If all sample families are `(δ, M)`-good with
`δ ≤ ε/8`, `20 M < |C r| ε` for both committees and `20 M ≤ n(ε - δ)`, and the committee
instances solve ε-BA when within their fault bound, then one level of ε-RPK with step-1 threshold
`2/3 - ε/4` achieves ε-BA on every input. -/
theorem lemma6_corrected_sampling {σ : Sampling n k} {adv : Adversary n}
    {C : Fin 2 → Finset (Fin n)} {ε δ M : ℚ} (hk : 0 < k) (hn : 0 < n) (hε : 0 < ε)
    (hε3 : ε < 1/3) (hδ0 : 0 ≤ δ) (hδ : δ ≤ ε/8)
    (hF : ((adv.F.card : ℕ) : ℚ) < n * (1/3 - ε)) (hsplit : CommitteeSplit C)
    (hM : ∀ r, 20 * M < (C r).card * ε) (hMn : 20 * M ≤ n * (ε - δ)) (hcomm : CommOK adv ε C)
    (hσ : SamplingGood δ M σ C) (inp : Fin n → Bool) :
    EpsBA ε adv.F inp (output (T1c ε) σ adv inp) := by
  obtain ⟨B, hB, hgood⟩ := exists_exceptional (adv := adv) (ε := ε) hσ inp
  exact lemma6_corrected ⟨hk, hn, hε, hε3, hδ0, hδ, hF, hsplit,
    fun r => lt_of_le_of_lt hB (hM r), hB.trans hMn, hcomm⟩ inp hgood

end ReachingUnivalency.RPK
