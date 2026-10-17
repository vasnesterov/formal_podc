import Papers.PODC2026.ReachingUnivalency.Counterexample
import Papers.PODC2026.ReachingUnivalency.Recursive

/-!
# Reaching Univalency — the protocol of §5 (Fig. 3) is not correct as specified

`Counterexample.lean` refutes Lemma 6 with black-box committees. Here the committees run the
paper's own recursive protocol (`Outcome` with the paper's step-1 threshold `2/3 - ε/2`): with
`n = 38`, `f = 5`, `ε = 1/5`, `k = 37`, and the sampling choices `σ38` (size 38) and `σ19`
(size 19) — both "not bad in any execution" in the strongest sense (`σ38_accurate`,
`σ19_accurate`: deviation `< ε/2` on every set, for every processor and step) — and **any**
sampling choices at the other sizes, the recursive protocol has an execution violating
ε-Agreement (`paper_protocol_fails`).

Inside the committees: `C₁` (5 Byzantine members, 14 correct members with value `1`) and `C₂`
(fault-free, inputs 16 zeros and 3 ones) see a unanimous-enough sample in step 1, so all their
correct members obtain grade 2 and output `1` resp. `0` whatever their own sub-committees do.
-/

namespace ReachingUnivalency.RPK.PaperFails

open Finset Counterexample

/-! ### A sharper deviation bound -/

lemma dev_eq_sum {n k : ℕ} (smp : Fin k → Fin n) (R S : Finset (Fin n)) (hR : ∀ j, smp j ∈ R) :
    dev smp R S = ∑ i ∈ S ∩ R, ((mult smp i : ℚ) / k - 1 / R.card) := by
  have h1 : ((univ.filter fun j => smp j ∈ S).card : ℚ) = ∑ i ∈ S ∩ R, (mult smp i : ℚ) := by
    rw [card_eq_sum_card_fiberwise (f := smp) (t := S ∩ R)]
    · push_cast
      refine sum_congr rfl fun i hi => ?_
      unfold mult
      congr 2
      ext j
      simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
      intro h; rw [h]; exact (mem_inter.mp hi).1
    · intro j hj
      exact mem_inter.mpr ⟨(mem_filter.mp hj).2, hR j⟩
  have h2 : ((S ∩ R).card : ℚ) / R.card = ∑ _i ∈ S ∩ R, (1 : ℚ) / R.card := by
    rw [sum_const, nsmul_eq_mul]; ring
  unfold dev
  rw [h1, h2, sum_div, ← sum_sub_distrib]

/-- The deviation on any set is at most the total-variation distance (positive or negative
part) between the empirical distribution of the sample and the uniform distribution on `R`. -/
theorem abs_dev_le_tv {n k : ℕ} (smp : Fin k → Fin n) (R S : Finset (Fin n))
    (hR : ∀ j, smp j ∈ R) :
    |dev smp R S| ≤ max (∑ i ∈ R, max ((mult smp i : ℚ) / k - 1 / R.card) 0)
      (∑ i ∈ R, max (1 / R.card - (mult smp i : ℚ) / k) 0) := by
  rw [dev_eq_sum smp R S hR, abs_le]
  constructor
  · refine neg_le.mp ?_
    refine le_trans ?_ (le_max_right _ _)
    rw [← sum_neg_distrib]
    calc ∑ i ∈ S ∩ R, -((mult smp i : ℚ) / k - 1 / R.card)
        ≤ ∑ i ∈ S ∩ R, max (1 / R.card - (mult smp i : ℚ) / k) 0 :=
          sum_le_sum fun i _ => by rw [neg_sub]; exact le_max_left _ _
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg inter_subset_right fun _ _ _ => le_max_right _ _
  · refine le_trans ?_ (le_max_left _ _)
    calc ∑ i ∈ S ∩ R, ((mult smp i : ℚ) / k - 1 / R.card)
        ≤ ∑ i ∈ S ∩ R, max ((mult smp i : ℚ) / k - 1 / R.card) 0 :=
          sum_le_sum fun i _ => le_max_left _ _
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg inter_subset_right fun _ _ _ => le_max_right _ _

/-! ### The sampling choice on 19 processors -/

/-- Cyclic samples: steps 1, 2 sample `j mod 19`; step 3 samples committee `{0..9}` as `j mod 10`
and committee `{10..18}` as `10 + j mod 9`. -/
def σ19 : Sampling 19 37 where
  val _ _ j := ⟨j.val % 19, by omega⟩
  resp _ _ j := ⟨j.val % 19, by omega⟩
  comm r _ j := if r = 0 then ⟨j.val % 10, by omega⟩ else ⟨10 + j.val % 9, by omega⟩

lemma σ19_comm_mem (r : Fin 2) (p : Fin 19) (j : Fin 37) : σ19.comm r p j ∈ comms 19 r := by
  revert r p j; decide +kernel

lemma tv_val : max (∑ i ∈ (univ : Finset (Fin 19)),
      max ((mult (fun j : Fin 37 => (⟨j.val % 19, by omega⟩ : Fin 19)) i : ℚ) / 37 -
        1 / (univ : Finset (Fin 19)).card) 0)
    (∑ i ∈ (univ : Finset (Fin 19)),
      max (1 / (univ : Finset (Fin 19)).card -
        (mult (fun j : Fin 37 => (⟨j.val % 19, by omega⟩ : Fin 19)) i : ℚ) / 37) 0) < 1/10 := by
  decide +kernel

lemma tv_comm (r : Fin 2) (p : Fin 19) :
    max (∑ i ∈ comms 19 r, max ((mult (σ19.comm r p) i : ℚ) / 37 - 1 / (comms 19 r).card) 0)
      (∑ i ∈ comms 19 r, max (1 / (comms 19 r).card - (mult (σ19.comm r p) i : ℚ) / 37) 0)
      < 1/10 := by
  revert r p; decide +kernel

/-- `σ19` is accurate to within `ε/2 = 1/10` on every set (hence not bad in any execution). -/
theorem σ19_accurate : Accurate σ19 (1/10) (comms 19) := by
  intro r p S
  refine ⟨?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (abs_dev_le_tv _ _ _ fun _ => mem_univ _) (by simpa [σ19] using tv_val)
  · exact lt_of_le_of_lt (abs_dev_le_tv _ _ _ fun _ => mem_univ _) (by simpa [σ19] using tv_val)
  · exact lt_of_le_of_lt (abs_dev_le_tv _ _ _ fun j => σ19_comm_mem r p j) (tv_comm r p)

/-- The top-level sampling choice of `Counterexample.lean`. -/
abbrev σ38 : Sampling 38 37 := Counterexample.σ

theorem σ38_accurate : Accurate σ38 (1/10) (comms 38) := by
  have : comms 38 = Counterexample.C := by funext r; revert r; decide
  rw [this]; exact sampling_accurate

/-! ### Congruence lemmas -/

section congr

variable {n k : ℕ}

lemma cnt_congr {F : Finset (Fin n)} {smp : Fin k → Fin n} {byz ans ans' : Fin n → Option Bool}
    (h : ∀ j, smp j ∉ F → ans (smp j) = ans' (smp j)) (b : Bool) :
    cnt F smp byz ans b = cnt F smp byz ans' b := by
  unfold cnt
  congr 1
  apply filter_congr
  intro j _
  unfold heard
  by_cases hj : smp j ∈ F
  · simp [hj]
  · simp [hj, h j hj]

lemma step1_congr {T : ℚ} {σ : Sampling n k} {adv : Adversary n} {r : Fin 2}
    {vals vals' : Fin n → Bool} {p : Fin n}
    (h : ∀ j, σ.val r p j ∉ adv.F → vals (σ.val r p j) = vals' (σ.val r p j)) :
    step1 T σ adv r vals p = step1 T σ adv r vals' p := by
  have h' : ∀ j, σ.val r p j ∉ adv.F →
      some (vals (σ.val r p j)) = some (vals' (σ.val r p j)) := fun j hj => by rw [h j hj]
  unfold step1
  dsimp only
  rw [cnt_congr (ans := fun q => some (vals q)) (ans' := fun q => some (vals' q)) h' true,
    cnt_congr (ans := fun q => some (vals q)) (ans' := fun q => some (vals' q)) h' false]

lemma step3_congr {σ : Sampling n k} {adv adv' : Adversary n} {r : Fin 2} {vg : Fin n → Bool × ℕ}
    {p : Fin n} (hF : adv'.F = adv.F) (hb : adv'.byzComm = adv.byzComm) (ht : adv'.tie = adv.tie)
    (h : ∀ j, σ.comm r p j ∉ adv.F → adv'.comm r (fun q => (vg q).1) (σ.comm r p j) =
      adv.comm r (fun q => (vg q).1) (σ.comm r p j)) :
    step3 σ adv' r vg p = step3 σ adv r vg p := by
  have h' : ∀ j, σ.comm r p j ∉ adv.F →
      some (adv'.comm r (fun q => (vg q).1) (σ.comm r p j)) =
      some (adv.comm r (fun q => (vg q).1) (σ.comm r p j)) := fun j hj => by rw [h j hj]
  unfold step3
  simp only [hF, hb, ht]
  rw [cnt_congr (ans := fun q => some (adv'.comm r (fun q => (vg q).1) q))
      (ans' := fun q => some (adv.comm r (fun q => (vg q).1) q)) h' true,
    cnt_congr (ans := fun q => some (adv'.comm r (fun q => (vg q).1) q))
      (ans' := fun q => some (adv.comm r (fun q => (vg q).1) q)) h' false]

end congr

/-! ### Executions inside the committees -/

/-- The paper's step-1 threshold for `ε = 1/5`. -/
abbrev T := Counterexample.T1

variable (smp : (m : ℕ) → Sampling m 37)

/-- An execution on 19 processors with Byzantine set `G`: Byzantine processors stay silent, and
the sub-committees run arbitrary executions (`outcome_exists`). -/
noncomputable def innerAdv (G : Finset (Fin 19)) : Adversary 19 where
  F := G
  byzVal _ _ _ := none
  byzResp _ _ _ := none
  byzComm _ _ _ := none
  tie _ _ := false
  comm r vals q :=
    if h : ∃ i, emb 19 r i = q then
      (outcome_exists T smp _ (subF (emb 19 r) G)).choose (vals ∘ emb 19 r) h.choose
    else false

lemma innerAdv_outcome (G : Finset (Fin 19)) :
    Outcome T smp 19 G (output T (smp 19) (innerAdv smp G)) := by
  refine Outcome.step (n := 19) (innerAdv smp G) (fun r => (comms 19 r).card) (emb 19)
    (fun r _ => (outcome_exists T smp _ (subF (emb 19 r) G)).choose) (by norm_num)
    (emb_isIndexing 19) (fun r _ => (outcome_exists T smp _ (subF (emb 19 r) G)).choose_spec) ?_
  intro r vals i
  have h : ∃ j, emb 19 r j = emb 19 r i := ⟨i, rfl⟩
  simp only [innerAdv, h, ↓reduceDIte]
  rw [emb_injective 19 r h.choose_spec]

/-- Re-indexing of the committees of `38` processors. -/
def e (r : Fin 2) (i : Fin 19) : Fin 38 := ⟨19 * r.val + i.val, by omega⟩

lemma e_isIndexing (r : Fin 2) : IsIndexing (comms 38 r) (e r) := by
  refine ⟨fun i j h => ?_, fun p => ?_⟩
  · simp only [e, Fin.mk.injEq] at h; exact Fin.ext (by omega)
  · fin_cases r
    · simp only [comms, Fin.zero_eta, Fin.isValue, ↓reduceIte, mem_filter, mem_univ, true_and, e,
        mul_zero, zero_add]
      constructor
      · intro hp; exact ⟨⟨p.val, by omega⟩, rfl⟩
      · rintro ⟨i, rfl⟩; simp only; omega
    · simp only [comms, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, mem_filter, mem_univ,
        true_and, e, mul_one]
      constructor
      · intro hp; exact ⟨⟨p.val - 19, by omega⟩, Fin.ext (by simp only; omega)⟩
      · rintro ⟨i, rfl⟩; simp only; omega

/-- `C₁`'s instance: Byzantine members `{14..18}`. -/
abbrev F0 : Finset (Fin 19) := subF (e 0) Counterexample.F
/-- `C₂`'s instance: no Byzantine member. -/
abbrev F1 : Finset (Fin 19) := subF (e 1) Counterexample.F

/-- The same Byzantine behaviour with trivial committees (steps 1 and 2 do not look at the
committees, so this computable adversary computes the same steps 1 and 2). -/
def silentAdv (G : Finset (Fin 19)) : Adversary 19 :=
  ⟨G, fun _ _ _ => none, fun _ _ _ => none, fun _ _ _ => none, fun _ _ => false, fun _ _ _ => false⟩

section inner

variable {smp}

lemma step1_inner (G : Finset (Fin 19)) :
    step1 T σ19 (innerAdv smp G) = step1 T σ19 (silentAdv G) := rfl

lemma step2_inner (G : Finset (Fin 19)) :
    step2 σ19 (innerAdv smp G) = step2 σ19 (silentAdv G) := rfl

lemma s1_inner0 (r : Fin 2) (p : Fin 19) :
    step1 T σ19 (innerAdv smp F0) r (fun _ => true) p = some true := by
  rw [step1_inner]; revert r p; decide +kernel

lemma s2_inner0 (r : Fin 2) (p : Fin 19) :
    2/3 * ((37 : ℕ) : ℚ) ≤ cnt F0 (σ19.resp r p) (fun _ => none) (fun _ => some true) true ∧
    (cnt F0 (σ19.resp r p) (fun _ => none) (fun _ => some true) false : ℚ) < ((37 : ℕ) : ℚ) / 3 := by
  revert r p; decide +kernel

/-- In `C₁` (14 correct members, all with value `1`) every round ends with all values `1`. -/
lemma round_inner0 (r : Fin 2) (vals : Fin 19 → Bool) (hv : ∀ i, i ∉ F0 → vals i = true) :
    round T σ19 (innerAdv smp F0) r vals = fun _ => true := by
  have h1 : step1 T σ19 (innerAdv smp F0) r vals = fun _ => some true := by
    funext p
    rw [step1_congr (vals' := fun _ => true) fun j hj => hv _ hj, s1_inner0]
  have h2 : step2 σ19 (innerAdv smp F0) r vals (fun _ => some true) = fun _ => (true, 2) := by
    funext p
    exact step2_eq_two (s2_inner0 r p).1 (s2_inner0 r p).2
  funext p
  show step3 σ19 _ r (step2 σ19 _ r vals (step1 T σ19 _ r vals)) p = true
  rw [h1, h2, step3_two rfl]

lemma output_inner0 (u : Fin 19 → Bool) (hu : ∀ i, i ∉ F0 → u i = true) (i : Fin 19) :
    output T σ19 (innerAdv smp F0) u i = true := by
  show round T σ19 _ 1 (round T σ19 _ 0 u) i = true
  rw [round_inner0 0 u hu, round_inner0 1 _ fun _ _ => rfl]

/-- The input of `C₂`'s instance in round 2 of the top-level execution. -/
def u1 : Fin 19 → Bool := fun i => decide (16 ≤ i.val)

lemma s1_inner1a : step1 T σ19 (innerAdv smp F1) 0 u1 = fun _ => some false := by
  rw [step1_inner]; funext p; revert p; decide +kernel

lemma s2_inner1a : step2 σ19 (innerAdv smp F1) 0 u1 (fun _ => some false) = fun _ => (false, 2) := by
  rw [step2_inner]; funext p; revert p; decide +kernel

lemma s1_inner1b (r : Fin 2) : step1 T σ19 (innerAdv smp F1) r (fun _ => false) = fun _ => some false := by
  rw [step1_inner]; funext p; revert r p; decide +kernel

lemma s2_inner1b (r : Fin 2) : step2 σ19 (innerAdv smp F1) r (fun _ => false) (fun _ => some false) =
    fun _ => (false, 2) := by
  rw [step2_inner]; funext p; revert r p; decide +kernel

lemma round_inner1b (r : Fin 2) : round T σ19 (innerAdv smp F1) r (fun _ => false) = fun _ => false := by
  funext p
  show step3 σ19 _ r (step2 σ19 _ r _ (step1 T σ19 _ r _)) p = false
  rw [s1_inner1b, s2_inner1b, step3_two rfl]

/-- In `C₂` (fault-free, inputs 16 zeros and 3 ones) everybody outputs `0`. -/
lemma output_inner1 : output T σ19 (innerAdv smp F1) u1 = fun _ => false := by
  have h0 : round T σ19 (innerAdv smp F1) 0 u1 = fun _ => false := by
    funext p
    show step3 σ19 _ 0 (step2 σ19 _ 0 _ (step1 T σ19 _ 0 _)) p = false
    rw [s1_inner1a, s2_inner1a, step3_two rfl]
  show round T σ19 _ 1 (round T σ19 _ 0 u1) = _
  rw [h0, round_inner1b]

end inner

/-! ### The top-level execution -/

/-- The top-level adversary of `Counterexample.lean`, except that the committee instances are
executions of the recursive protocol on the committees. -/
noncomputable def advP : Adversary 38 :=
  { Counterexample.adv with
    comm := fun r vals q =>
      if h : ∃ i, e r i = q then
        output T (smp 19) (innerAdv smp (subF (e r) Counterexample.F)) (vals ∘ e r) h.choose
      else false }

lemma advP_outcome : Outcome T smp 38 Counterexample.F (output T (smp 38) (advP smp)) := by
  refine Outcome.step (n := 38) (advP smp) (fun _ => 19) e
    (fun r _ => output T (smp 19) (innerAdv smp (subF (e r) Counterexample.F))) (by norm_num)
    e_isIndexing (fun r _ => innerAdv_outcome smp _) ?_
  intro r vals i
  have h : ∃ j, e r j = e r i := ⟨i, rfl⟩
  simp only [advP, h, ↓reduceDIte]
  rw [(e_isIndexing r).1 h.choose_spec]

variable {smp}

lemma advP_comm0 (h19 : smp 19 = σ19) (vals : Fin 38 → Bool)
    (hv : ∀ i : Fin 19, i ∉ F0 → vals (e 0 i) = true) (q : Fin 38) (hq : q.val < 19) :
    (advP smp).comm 0 vals q = true := by
  have h : ∃ i, e 0 i = q := ⟨⟨q.val, hq⟩, Fin.ext (by simp [e])⟩
  simp only [advP, h, ↓reduceDIte]
  rw [h19]
  exact output_inner0 _ hv _

lemma advP_comm1 (h19 : smp 19 = σ19) (vals : Fin 38 → Bool) (hv : vals ∘ e 1 = u1)
    (q : Fin 38) (hq : 19 ≤ q.val) : (advP smp).comm 1 vals q = false := by
  have h : ∃ i, e 1 i = q := ⟨⟨q.val - 19, by omega⟩, Fin.ext (by simp [e]; omega)⟩
  simp only [advP, h, ↓reduceDIte]
  rw [h19, hv, output_inner1]

lemma vals1P (h19 : smp 19 = σ19) :
    valsAt T σ38 (advP smp) inp 1 = valsAt T σ38 adv inp 1 := by
  funext p
  show step3 σ38 (advP smp) 0 (vgAt T σ38 adv inp 0) p = step3 σ38 adv 0 (vgAt T σ38 adv inp 0) p
  refine step3_congr rfl rfl rfl fun j _ => ?_
  have hq : (σ38.comm 0 p j).val < 19 := by simp [σ38, Counterexample.σ]; omega
  rw [advP_comm0 h19 _ (by rw [vg0]; decide +kernel) _ hq]
  show true = majVal (C 0) Counterexample.F (fun q => (vgAt T σ38 adv inp 0 q).1)
  rw [vg0]; decide +kernel

lemma outputP (h19 : smp 19 = σ19) : output T σ38 (advP smp) inp = output T σ38 adv inp := by
  show round T σ38 (advP smp) 1 (valsAt T σ38 (advP smp) inp 1) =
    round T σ38 adv 1 (valsAt T σ38 adv inp 1)
  rw [vals1P h19]
  funext p
  show step3 σ38 (advP smp) 1 (vgAt T σ38 adv inp 1) p = step3 σ38 adv 1 (vgAt T σ38 adv inp 1) p
  refine step3_congr rfl rfl rfl fun j _ => ?_
  have hq : 19 ≤ (σ38.comm 1 p j).val := by simp [σ38, Counterexample.σ]
  rw [advP_comm1 h19 _ (by funext i; rw [vg1]; revert i; decide +kernel) _ hq]
  show false = majVal (C 1) Counterexample.F (fun q => (vgAt T σ38 adv inp 1 q).1)
  rw [vg1]; decide +kernel

/-- **The protocol of §5 is not correct as specified.** With the paper's step-1 threshold, the
sampling choices `σ38` and `σ19` (accurate to within `ε/2` on every set: `σ38_accurate`,
`σ19_accurate`), and *any* sampling choices at the other sizes, the recursive ε-RPK on `38`
processors with `5 < 38(1/3 - 1/5)` Byzantine processors has an execution violating ε-BA. -/
theorem paper_protocol_fails (smp : (m : ℕ) → Sampling m 37) (h38 : smp 38 = σ38)
    (h19 : smp 19 = σ19) :
    ∃ (F : Finset (Fin 38)) (out : (Fin 38 → Bool) → Fin 38 → Bool) (inp : Fin 38 → Bool),
      Outcome (2/3 - (1/5 : ℚ)/2) smp 38 F out ∧ ((F.card : ℕ) : ℚ) < 38 * (1/3 - 1/5) ∧
      ¬ EpsBA (1/5) F inp (out inp) := by
  refine ⟨Counterexample.F, output T (smp 38) (advP smp), inp, advP_outcome smp, ?_, ?_⟩
  · rw [card_F]; norm_num
  · rw [h38, outputP h19]
    exact not_epsBA

end ReachingUnivalency.RPK.PaperFails
