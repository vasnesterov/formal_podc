import Papers.PODC2026.ReachingUnivalency.EpsBA

/-!
# Reaching Univalency — §4: one level of (Probabilistic) ε-RPK

The protocol of Fig. 2/Fig. 3 at one level of the recursion, with the two recursive calls on the
committees treated as black boxes (as in the paper's analysis: "it does not matter exactly how the
committees carry out ε-BA, so long as they do so correctly").

**Model.** Processors `Fin n`, a static set `F` of Byzantine processors, two committees `C 0`,
`C 1` (the paper's `C₁`, `C₂`). A *sampling choice* fixes, for each round `r ∈ {0,1}`, each
processor `p` and each of the three steps, the `k` processors (with repetitions) whose values `p`
learns. A sampled correct processor reports its true value; a sampled Byzantine processor `q`
reports to `p` an arbitrary `Option Bool` chosen by the adversary (`none` = `⊥`/silence).
The committee ε-BA instance of round `r` is an arbitrary function `comm r` from the input vector to
the output vector (chosen by the adversary), constrained only by `CommOK`: if the committee has
fewer than `|C r|(1/3 - ε)` faulty members, its outcome satisfies ε-BA. Majority ties in step 3 are
broken by the adversary (`tie`).

Step 1 uses a threshold `T1` (the paper: `T1 = 2/3 - ε/2`; our corrected protocol in
`Corrected.lean` uses `2/3 - ε/4`); steps 2 and 3 are as in the paper.

The paper's notion of a *bad* sampling choice (§4.2) is `NotBad`; the per-processor deviation of a
sample from the population is `dev`. `Lemma6Claim` is Lemma 6 as stated.
-/

namespace ReachingUnivalency.RPK

open Finset

variable {n k : ℕ}

/-- A sampling choice: `val r p`, `resp r p`, `comm r p` are the `k` processors sampled by `p` in
steps 1, 2, 3 of round `r`. -/
structure Sampling (n k : ℕ) where
  /-- Step 1 samples (response set `Π`). -/
  val : Fin 2 → Fin n → Fin k → Fin n
  /-- Step 2 samples (response set `Π`). -/
  resp : Fin 2 → Fin n → Fin k → Fin n
  /-- Step 3 samples (response set `C r`). -/
  comm : Fin 2 → Fin n → Fin k → Fin n

/-- Everything chosen by the adversary: the Byzantine set, the Byzantine answers (`byz… r q p`:
what the Byzantine `q` reports to `p`), tie-breaking, and the outcome of the committee instances. -/
structure Adversary (n : ℕ) where
  /-- Byzantine processors. -/
  F : Finset (Fin n)
  /-- Byzantine answers in step 1. -/
  byzVal : Fin 2 → Fin n → Fin n → Option Bool
  /-- Byzantine answers in step 2. -/
  byzResp : Fin 2 → Fin n → Fin n → Option Bool
  /-- Byzantine answers in step 3. -/
  byzComm : Fin 2 → Fin n → Fin n → Option Bool
  /-- Tie-breaking of the step-3 majority. -/
  tie : Fin 2 → Fin n → Bool
  /-- Outputs of the committee ε-BA instance of round `r`, as a function of its inputs. -/
  comm : Fin 2 → (Fin n → Bool) → Fin n → Bool

/-- What `p` hears from the sampled processor `q`. -/
def heard (F : Finset (Fin n)) (byz : Fin n → Option Bool) (ans : Fin n → Option Bool)
    (q : Fin n) : Option Bool :=
  if q ∈ F then byz q else ans q

/-- Number of samples reporting `b`. -/
def cnt (F : Finset (Fin n)) (smp : Fin k → Fin n) (byz ans : Fin n → Option Bool) (b : Bool) : ℕ :=
  (univ.filter fun j => heard F byz ans (smp j) = some b).card

variable (T1 : ℚ) (σ : Sampling n k) (adv : Adversary n)

/-- Step 1: the response value. -/
def step1 (r : Fin 2) (vals : Fin n → Bool) (p : Fin n) : Option Bool :=
  let c := cnt adv.F (σ.val r p) (adv.byzVal r · p) (fun q => some (vals q))
  if T1 * k ≤ c true then some true else if T1 * k ≤ c false then some false else none

/-- Step 2: the new value and the grade. -/
def step2 (r : Fin 2) (vals : Fin n → Bool) (resp : Fin n → Option Bool) (p : Fin n) :
    Bool × ℕ :=
  let c := cnt adv.F (σ.resp r p) (adv.byzResp r · p) resp
  if 2/3 * (k : ℚ) ≤ c true then (true, 2)
  else if 2/3 * (k : ℚ) ≤ c false then (false, 2)
  else if (k : ℚ)/3 ≤ c true ∧ ¬ (k : ℚ)/3 ≤ c false then (true, 1)
  else if (k : ℚ)/3 ≤ c false ∧ ¬ (k : ℚ)/3 ≤ c true then (false, 1)
  else (vals p, 0)

/-- Step 3: keep the value if the grade is 2, otherwise adopt the majority of the sampled
committee outputs. -/
def step3 (r : Fin 2) (vg : Fin n → Bool × ℕ) (p : Fin n) : Bool :=
  if (vg p).2 = 2 then (vg p).1 else
    let outs := adv.comm r (fun q => (vg q).1)
    let c := cnt adv.F (σ.comm r p) (adv.byzComm r · p) (fun q => some (outs q))
    if c false < c true then true else if c true < c false then false else adv.tie r p

/-- One round. -/
def round (r : Fin 2) (vals : Fin n → Bool) : Fin n → Bool :=
  step3 σ adv r (step2 σ adv r vals (step1 T1 σ adv r vals))

/-- Values at the start of round `r`. -/
def valsAt (inp : Fin n → Bool) : Fin 2 → Fin n → Bool
  | 0 => inp
  | 1 => round T1 σ adv 0 inp

/-- Step-1 responses of round `r`. -/
def respAt (inp : Fin n → Bool) (r : Fin 2) : Fin n → Option Bool :=
  step1 T1 σ adv r (valsAt T1 σ adv inp r)

/-- Values and grades after step 2 of round `r`. -/
def vgAt (inp : Fin n → Bool) (r : Fin 2) : Fin n → Bool × ℕ :=
  step2 σ adv r (valsAt T1 σ adv inp r) (respAt T1 σ adv inp r)

/-- Outputs of the committee instance of round `r`. -/
def outsAt (inp : Fin n → Bool) (r : Fin 2) : Fin n → Bool :=
  adv.comm r (fun q => (vgAt T1 σ adv inp r q).1)

/-- The outputs of the protocol. -/
def output (inp : Fin n → Bool) : Fin n → Bool := round T1 σ adv 1 (round T1 σ adv 0 inp)

/-! ### Samples, deviations, the paper's bad sampling choices -/

/-- Deviation of the sample `smp` from the response set `R` on the set `S`:
`(fraction of samples in S) - (fraction of R in S)`. -/
def dev (smp : Fin k → Fin n) (R S : Finset (Fin n)) : ℚ :=
  ((univ.filter fun j => smp j ∈ S).card : ℚ) / k - ((S ∩ R).card : ℚ) / R.card

/-- Multiplicity of `i` in the sample `smp`. -/
def mult (smp : Fin k → Fin n) (i : Fin n) : ℕ := (univ.filter fun j => smp j = i).card

/-- The deviation on any set is bounded by the `ℓ¹` distance between the sample's empirical
distribution and the uniform distribution on `R`. -/
theorem abs_dev_le (smp : Fin k → Fin n) (R S : Finset (Fin n)) (hR : ∀ j, smp j ∈ R) :
    |dev smp R S| ≤ ∑ i ∈ R, |(mult smp i : ℚ) / k - 1 / R.card| := by
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
  calc |∑ i ∈ S ∩ R, ((mult smp i : ℚ) / k - 1 / R.card)|
      ≤ ∑ i ∈ S ∩ R, |(mult smp i : ℚ) / k - 1 / R.card| := abs_sum_le_sum_abs _ _
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg inter_subset_right fun _ _ _ => abs_nonneg _

/-- Correct processors whose answer is `some b`. -/
def corr (F : Finset (Fin n)) (ans : Fin n → Option Bool) (b : Bool) : Finset (Fin n) :=
  univ.filter fun q => q ∉ F ∧ ans q = some b

/-- §4.2: the sampling choice is *bad for `p`* if for some step `s` and bit `b` the fraction
`α_{s,b}` of the response set that is correct with response value `b` and the fraction
`α_{s,b,p}` of `p`'s samples that are correct with response value `b` differ by at least `ε/2`.
(`α_{s,b,p} - α_{s,b} = dev`.) -/
def BadFor (ε : ℚ) (C : Fin 2 → Finset (Fin n)) (inp : Fin n → Bool) (p : Fin n) : Prop :=
  ∃ r : Fin 2, ∃ b : Bool,
    ε / 2 ≤ |dev (σ.val r p) univ (corr adv.F (fun q => some (valsAt T1 σ adv inp r q)) b)| ∨
    ε / 2 ≤ |dev (σ.resp r p) univ (corr adv.F (respAt T1 σ adv inp r) b)| ∨
    ε / 2 ≤ |dev (σ.comm r p) (C r) (corr adv.F (fun q => some (outsAt T1 σ adv inp r q)) b)|

/-- §4.2: sampling is *not bad*: it is bad for fewer than `nε/4` correct processors. -/
def NotBad (ε : ℚ) (C : Fin 2 → Finset (Fin n)) (inp : Fin n → Bool) : Prop :=
  open Classical in
  (((univ.filter fun p => p ∉ adv.F ∧ BadFor T1 σ adv ε C inp p).card : ℕ) : ℚ) < n * ε / 4

/-- §5's notion, in its strongest per-processor form: for every step, every processor and every
set `S` of processors (in particular for every "configuration"), the sample deviates from the
response set by less than `δ`. -/
def Accurate (δ : ℚ) (C : Fin 2 → Finset (Fin n)) : Prop :=
  ∀ r p (S : Finset (Fin n)), |dev (σ.val r p) univ S| < δ ∧ |dev (σ.resp r p) univ S| < δ ∧
    |dev (σ.comm r p) (C r) S| < δ

/-- An accurate sampling choice (to within `ε/2`) is not bad. -/
theorem notBad_of_accurate {ε : ℚ} {C : Fin 2 → Finset (Fin n)} (inp : Fin n → Bool)
    (hacc : Accurate σ (ε / 2) C) (hpos : 0 < (n : ℚ) * ε) : NotBad T1 σ adv ε C inp := by
  have hnb : ∀ p, ¬ BadFor T1 σ adv ε C inp p := by
    rintro p ⟨r, b, h⟩
    have acc := hacc r p
    rcases h with h | h | h
    · exact not_lt.mpr h (acc _).1
    · exact not_lt.mpr h (acc _).2.1
    · exact not_lt.mpr h (acc _).2.2
  unfold NotBad
  classical
  rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun p _ h => hnb p h.2)]
  simp only [Nat.cast_zero]
  positivity

/-- The committees partition `Π` and differ in size by at most one. -/
def CommitteeSplit (C : Fin 2 → Finset (Fin n)) : Prop :=
  Disjoint (C 0) (C 1) ∧ C 0 ∪ C 1 = univ ∧ (C 0).card ≤ (C 1).card + 1 ∧
    (C 1).card ≤ (C 0).card + 1

/-- Step-3 samples are taken from the committee. -/
def SamplesInCommittee (C : Fin 2 → Finset (Fin n)) : Prop := ∀ r p j, σ.comm r p j ∈ C r

/-- The committee instances solve ε-BA whenever the committee has fewer than `|C r|(1/3 - ε)`
faulty members (the recursion hypothesis). -/
def CommOK (ε : ℚ) (C : Fin 2 → Finset (Fin n)) : Prop :=
  ∀ r vals, (((C r ∩ adv.F).card : ℕ) : ℚ) < (C r).card * (1/3 - ε) →
    EpsBAOn (C r) ε adv.F vals (adv.comm r vals)

end ReachingUnivalency.RPK

namespace ReachingUnivalency.RPK

open Finset

/-- **Lemma 6 as stated in the paper**: if `n > 2`, `ε ∈ (0, 1/3)`, `f < n(1/3 - ε)` and the
sampling is not bad, then Probabilistic ε-RPK (step-1 threshold `2/3 - ε/2`) achieves ε-BA. -/
def Lemma6Claim : Prop :=
  ∀ (n k : ℕ) (ε : ℚ) (C : Fin 2 → Finset (Fin n)) (σ : Sampling n k) (adv : Adversary n)
    (inp : Fin n → Bool),
    2 < n → 0 < k → 0 < ε → ε < 1/3 → ((adv.F.card : ℕ) : ℚ) < n * (1/3 - ε) →
    CommitteeSplit C → SamplesInCommittee σ C → CommOK adv ε C →
    NotBad (2/3 - ε/2) σ adv ε C inp →
    EpsBA ε adv.F inp (output (2/3 - ε/2) σ adv inp)

end ReachingUnivalency.RPK
