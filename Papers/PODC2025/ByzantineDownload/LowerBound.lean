import Mathlib

/-!
# The one-round lower bound (§3 of Augustine et al., arXiv 2412.19649)

Data Retrieval model with `n` peers (`Fin n`) and an `n`-bit source `X : Fin n → Bool`
(the paper uses `n` both for the number of peers and of bits in §3). A **one-round randomized
algorithm** (class `A(q, 1)`): every peer `v` draws a private random string `R v : Ω v`
(independently of the other peers), queries the set of bits `qry v (R v)` in the query sub-round
(the set cannot depend on `X`: nothing has been received yet), sends to every peer `u` a message
`msg v (R v) a u` that depends on its random string and on the answers `a` of its queries, and
finally outputs `out v (R v) a inbox`, an `n`-bit vector.

Randomness: each `Ω v` is a finite type with probability weights `w v`; the random profile
`R : (v : Fin n) → Ω v` has probability `∏ v, w v (R v)` (independent private coins).

Adversary (the "weak" non-adaptive adversary of Definition 3.1): it fixes the input `X`, a set `Byz`
of `(n-1)/2` Byzantine peers, and the messages of the Byzantine peers as a function of their own
random strings. The adversary used in the proof is the paper's: the Byzantine peers run the
algorithm honestly, but on the input `X` with bit `ℓ` flipped.

Main results: `lemma_3_3` (some bit is skipped by some peer with probability `≥ 1 - 1/e`),
`claim_3_5` (indistinguishability), `theorem_3_6` (every algorithm in `A(n-1, 1)` fails with
probability `≥ (1 - 1/e)/4` against this adversary). Since the Byzantine peers send exactly the
messages of honest peers, the bound also holds in the broadcast model (`theorem_3_6_broadcast`).
-/

namespace Podc.ByzantineDownload.LowerBound

open Finset

variable {n : ℕ} {Ω : Fin n → Type} {M : Type}

/-- A one-round randomized algorithm in the DR model: queries, messages and output of each peer
as functions of its private random string (and, for messages and output, of the query answers
and the received messages). -/
structure OneRoundAlg (n : ℕ) (Ω : Fin n → Type) (M : Type) where
  /-- The bits `v` queries in the (single) query sub-round. -/
  qry : (v : Fin n) → Ω v → Finset (Fin n)
  /-- The message `v` sends to `u`, given its random string and its query answers. -/
  msg : (v : Fin n) → Ω v → (Fin n → Option Bool) → Fin n → M
  /-- The output of `v`, given its random string, its query answers and its inbox. -/
  out : (v : Fin n) → Ω v → (Fin n → Option Bool) → (Fin n → M) → (Fin n → Bool)

/-- The answers a peer querying the set `Q` gets from the source `X`. -/
def answers (Q : Finset (Fin n)) (X : Fin n → Bool) : Fin n → Option Bool :=
  fun i => if i ∈ Q then some (X i) else none

/-- Independent private coins: a probability distribution on each `Ω v`. -/
structure Coins (n : ℕ) (Ω : Fin n → Type) [∀ v, Fintype (Ω v)] where
  /-- The probability weights of peer `v`'s random strings. -/
  w : (v : Fin n) → Ω v → ℝ
  nonneg : ∀ v ω, 0 ≤ w v ω
  sum_one : ∀ v, ∑ ω, w v ω = 1

variable [∀ v, Fintype (Ω v)]

/-- The probability of a random profile (product distribution). -/
def Coins.prob (μ : Coins n Ω) (R : (v : Fin n) → Ω v) : ℝ := ∏ v, μ.w v (R v)

open Classical in
/-- The probability of an event on random profiles. -/
noncomputable def Coins.P (μ : Coins n Ω) (E : ((v : Fin n) → Ω v) → Prop) : ℝ :=
  ∑ R, if E R then μ.prob R else 0

/-- The inbox of `v`: honest peers send `A`'s messages for the true input `X`, Byzantine peers
`u ∈ Byz` send `byz u (R u) v`. -/
def inbox (A : OneRoundAlg n Ω M) (X : Fin n → Bool) (Byz : Finset (Fin n))
    (byz : (u : Fin n) → Ω u → Fin n → M) (R : (v : Fin n) → Ω v) (v : Fin n) : Fin n → M :=
  fun u => if u ∈ Byz then byz u (R u) v else A.msg u (R u) (answers (A.qry u (R u)) X) v

/-- The execution `EX(X, Byz, R)` fails: some nonfaulty peer outputs a wrong vector. -/
def Fails (A : OneRoundAlg n Ω M) (X : Fin n → Bool) (Byz : Finset (Fin n))
    (byz : (u : Fin n) → Ω u → Fin n → M) (R : (v : Fin n) → Ω v) : Prop :=
  ∃ v ∉ Byz, A.out v (R v) (answers (A.qry v (R v)) X) (inbox A X Byz byz R v) ≠ X

/-- `X` with bit `ℓ` inverted (`X^inv` in the paper). -/
def flip (X : Fin n → Bool) (ℓ : Fin n) : Fin n → Bool := Function.update X ℓ (!X ℓ)

/-- The paper's Byzantine strategy: run `A` honestly, but on the input `X^inv`. -/
def runOnFlip (A : OneRoundAlg n Ω M) (X : Fin n → Bool) (ℓ : Fin n) :
    (u : Fin n) → Ω u → Fin n → M :=
  fun u ω => A.msg u ω (answers (A.qry u ω) (flip X ℓ))

/-- `A ∈ A(n-1, 1)`: every peer queries at most `n - 1` bits, whatever its random string. -/
def OneRoundAlg.QueryBound (A : OneRoundAlg n Ω M) (q : ℕ) : Prop := ∀ v ω, (A.qry v ω).card ≤ q

/-! ### Elementary facts about the product distribution -/

lemma Coins.prob_nonneg (μ : Coins n Ω) (R : (v : Fin n) → Ω v) : 0 ≤ μ.prob R :=
  Finset.prod_nonneg fun v _ => μ.nonneg v (R v)

lemma Coins.sum_prob (μ : Coins n Ω) : ∑ R, μ.prob R = 1 := by
  simp only [Coins.prob]
  rw [← Fintype.prod_sum]
  simp [μ.sum_one]

lemma Coins.P_nonneg (μ : Coins n Ω) (E : ((v : Fin n) → Ω v) → Prop) : 0 ≤ μ.P E :=
  Finset.sum_nonneg fun R _ => by split_ifs <;> simp [μ.prob_nonneg R]

lemma Coins.P_compl (μ : Coins n Ω) (E : ((v : Fin n) → Ω v) → Prop) :
    μ.P E = 1 - μ.P (fun R => ¬ E R) := by
  have h : μ.P E + μ.P (fun R => ¬ E R) = 1 := by
    simp only [Coins.P]
    rw [← Finset.sum_add_distrib, ← μ.sum_prob]
    refine Finset.sum_congr rfl fun R _ => ?_
    by_cases hE : E R <;> simp [hE]
  linarith

open Classical in
/-- Independence: the probability that every peer's random string satisfies its own predicate is
the product of the individual probabilities. -/
lemma Coins.P_forall (μ : Coins n Ω) (S : (v : Fin n) → Ω v → Prop) :
    μ.P (fun R => ∀ v, S v (R v)) = ∏ v, ∑ ω, if S v ω then μ.w v ω else 0 := by
  simp only [Coins.P, Coins.prob]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun R _ => ?_
  rw [Finset.prod_ite_zero]
  simp

/-- `2 * m + 1` choose `m` is at most twice `2 * m` choose `m`. -/
lemma choose_le_two_mul (m : ℕ) : (2 * m + 1).choose m ≤ 2 * (2 * m).choose m := by
  rcases m with _ | k
  · simp
  · rw [Nat.choose_succ_succ']
    have h := Nat.choose_le_middle k (2 * (k + 1))
    rw [show 2 * (k + 1) / 2 = k + 1 by omega] at h
    omega

/-- Counting via the involution `Byz ↦ V \ (Byz ∪ {v})` on the `m`-sets avoiding `v`
(here `n = 2m + 1`). -/
lemma choose_le_sum_involution {m : ℕ} (hm : n = 2 * m + 1) (v : Fin n)
    (f g : Finset (Fin n) → ℝ) (hf : ∀ s, 0 ≤ f s) (hg : ∀ s, 0 ≤ g s)
    (h : ∀ s, v ∉ s → 1 ≤ f s + g (univ \ insert v s)) :
    ((n - 1).choose m : ℝ) ≤ ∑ s ∈ powersetCard m (univ : Finset (Fin n)), (f s + g s) := by
  classical
  set Bv := powersetCard m ((univ : Finset (Fin n)).erase v) with hBv
  have hcard : (Bv.card : ℝ) = ((n - 1).choose m : ℝ) := by
    rw [hBv, card_powersetCard, card_erase_of_mem (mem_univ v), card_univ, Fintype.card_fin]
  have hsub : Bv ⊆ powersetCard m univ := powersetCard_mono (subset_univ _)
  have hmaps : ∀ s ∈ Bv, univ \ insert v s ∈ Bv := by
    intro s hs
    rw [hBv, mem_powersetCard] at hs ⊢
    have hvs : v ∉ s := fun h' => by simpa using hs.1 h'
    refine ⟨fun x hx => ?_, ?_⟩
    · simp only [mem_sdiff, mem_univ, mem_insert, not_or, true_and] at hx
      simp [hx.1]
    · rw [card_univ_sdiff, card_insert_of_notMem hvs, Fintype.card_fin, hs.2]
      omega
  have hinv : ∀ s ∈ Bv, univ \ insert v (univ \ insert v s) = s := by
    intro s hs
    rw [hBv, mem_powersetCard] at hs
    have hvs : v ∉ s := fun h' => by simpa using hs.1 h'
    ext x
    by_cases hx : x = v
    · subst hx; simp [hvs]
    · simp [hx]
  have hg' : ∑ s ∈ Bv, g (univ \ insert v s) = ∑ s ∈ Bv, g s :=
    Finset.sum_nbij' (fun s => univ \ insert v s) (fun s => univ \ insert v s) hmaps hmaps
      hinv hinv (fun _ _ => rfl)
  calc ((n - 1).choose m : ℝ) = ∑ s ∈ Bv, (1 : ℝ) := by simp [hcard]
    _ ≤ ∑ s ∈ Bv, (f s + g (univ \ insert v s)) := by
        refine Finset.sum_le_sum fun s hs => h s ?_
        rw [hBv, mem_powersetCard] at hs
        exact fun h' => by simpa using hs.1 h'
    _ = ∑ s ∈ Bv, (f s + g s) := by rw [Finset.sum_add_distrib, hg', ← Finset.sum_add_distrib]
    _ ≤ ∑ s ∈ powersetCard m univ, (f s + g s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun s _ _ => add_nonneg (hf s) (hg s)

/-- **Lemma 3.3.** If every peer always skips some bit, then some bit `ℓ` is skipped by some
peer with probability at least `1 - 1/e`. -/
theorem lemma_3_3 (hn : 0 < n) (A : OneRoundAlg n Ω M) (hA : A.QueryBound (n - 1)) (μ : Coins n Ω) :
    ∃ ℓ : Fin n, 1 - Real.exp (-1) ≤ μ.P (fun R => ∃ v, ℓ ∉ A.qry v (R v)) := by
  classical
  set q : Fin n → Fin n → ℝ := fun v i => ∑ ω, if i ∈ A.qry v ω then μ.w v ω else 0 with hq
  have hq0 : ∀ v i, 0 ≤ q v i := fun v i =>
    Finset.sum_nonneg fun ω _ => by split_ifs <;> simp [μ.nonneg]
  have hsum : ∀ v, ∑ i, q v i ≤ n - 1 := by
    intro v
    simp only [q]
    rw [Finset.sum_comm]
    calc ∑ ω, ∑ i, (if i ∈ A.qry v ω then μ.w v ω else 0)
          = ∑ ω, ((A.qry v ω).card : ℝ) * μ.w v ω := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ ω, ((n : ℝ) - 1) * μ.w v ω := by
          refine Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_right ?_ (μ.nonneg v ω)
          have h1 : ((A.qry v ω).card : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hA v ω
          rw [Nat.cast_sub (by omega)] at h1
          simpa using h1
      _ = n - 1 := by rw [← Finset.mul_sum, μ.sum_one, mul_one]
  obtain ⟨ℓ, -, hℓ⟩ : ∃ ℓ ∈ (univ : Finset (Fin n)), (1 : ℝ) ≤ ∑ v, (1 - q v ℓ) := by
    have hne : (univ : Finset (Fin n)).Nonempty := univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
    refine Finset.exists_le_of_sum_le hne ?_
    rw [Finset.sum_comm]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    have h2 : ∑ v : Fin n, ∑ ℓ, q v ℓ ≤ ∑ v : Fin n, ((n : ℝ) - 1) :=
      Finset.sum_le_sum fun v _ => hsum v
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    nlinarith
  refine ⟨ℓ, ?_⟩
  rw [μ.P_compl]
  have hall : μ.P (fun R => ¬ ∃ v, ℓ ∉ A.qry v (R v)) = ∏ v, q v ℓ := by
    have hfun : (fun R : (v : Fin n) → Ω v => ¬ ∃ v, ℓ ∉ A.qry v (R v)) =
        fun R => ∀ v, (fun v ω => ℓ ∈ A.qry v ω) v (R v) := by
      funext R; simp
    rw [hfun, μ.P_forall (fun v ω => ℓ ∈ A.qry v ω)]
    simp only [q]
    congr!
  rw [hall]
  have hprod : ∏ v, q v ℓ ≤ Real.exp (-1) := by
    calc ∏ v, q v ℓ ≤ ∏ v, Real.exp (q v ℓ - 1) :=
          Finset.prod_le_prod₀ (fun v _ => hq0 v ℓ)
            (fun v _ => by linarith [Real.add_one_le_exp (q v ℓ - 1)])
      _ = Real.exp (∑ v, (q v ℓ - 1)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (-1) := by
          apply Real.exp_le_exp.mpr
          have : ∑ v, (q v ℓ - 1) = - ∑ v, (1 - q v ℓ) := by
            rw [← Finset.sum_neg_distrib]; simp
          linarith
  linarith

/-- **Claim 3.5.** If peer `v` does not query `ℓ`, it cannot distinguish the execution on `X` with
Byzantine set `Byz ∌ v` from the execution on `X^inv` with Byzantine set `V \ (Byz ∪ {v})`
(both with the paper's Byzantine strategy); hence one of them fails. -/
theorem claim_3_5 (A : OneRoundAlg n Ω M) (X : Fin n → Bool) (ℓ : Fin n) (Byz : Finset (Fin n))
    (R : (v : Fin n) → Ω v) (v : Fin n) (hv : v ∉ Byz) (hℓ : ℓ ∉ A.qry v (R v)) :
    Fails A X Byz (runOnFlip A X ℓ) R ∨
      Fails A (flip X ℓ) (univ \ insert v Byz) (runOnFlip A (flip X ℓ) ℓ) R := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  simp only [Fails, not_exists, not_and, not_not] at h1 h2
  have e1 := h1 v hv
  have e2 := h2 v (by simp)
  have hans : answers (A.qry v (R v)) (flip X ℓ) = answers (A.qry v (R v)) X := by
    funext i
    simp only [answers]
    split_ifs with hi
    · have hiℓ : i ≠ ℓ := fun h => hℓ (h ▸ hi)
      simp [flip, Function.update_of_ne hiℓ]
    · rfl
  have hff : flip (flip X ℓ) ℓ = X := by
    funext i
    by_cases hi : i = ℓ
    · subst hi; simp [flip]
    · simp [flip, Function.update_of_ne hi]
  have hinbox : inbox A (flip X ℓ) (univ \ insert v Byz) (runOnFlip A (flip X ℓ) ℓ) R v =
      inbox A X Byz (runOnFlip A X ℓ) R v := by
    funext u
    simp only [inbox, runOnFlip, hff]
    by_cases hu : u = v
    · subst hu; simp [hv, hans]
    · by_cases hb : u ∈ Byz
      · simp [hb]
      · simp [hb, hu]
  rw [hans, hinbox, e1] at e2
  have := congr_fun e2 ℓ
  simp [flip] at this

/-- **Theorem 3.6** (Lemma 3.4). With `n` peers, `n` odd, and at most `(n-1)/2` Byzantine peers,
every one-round algorithm in which each peer queries at most `n - 1` bits fails with probability at
least `(1 - 1/e)/4` against the paper's adversary: some input `X`, some set of `(n-1)/2` Byzantine
peers that run the algorithm on `X` with one bit flipped. -/
theorem theorem_3_6 (hn : Odd n) (A : OneRoundAlg n Ω M) (hA : A.QueryBound (n - 1))
    (μ : Coins n Ω) :
    ∃ (X : Fin n → Bool) (ℓ : Fin n) (Byz : Finset (Fin n)), Byz.card = (n - 1) / 2 ∧
      (1 - Real.exp (-1)) / 4 ≤ μ.P (Fails A X Byz (runOnFlip A X ℓ)) := by
  classical
  obtain ⟨m, hm⟩ := hn
  rw [show (n - 1) / 2 = m by omega]
  obtain ⟨ℓ, hℓ⟩ := lemma_3_3 (by omega) A hA μ
  set X0 : Fin n → Bool := fun _ => false with hX0
  set X1 := flip X0 ℓ with hX1
  set c := 1 - Real.exp (-1) with hc
  by_contra hcon
  push Not at hcon
  have hp := μ.prob_nonneg
  -- per random profile: an `ℓ`-defective profile makes at least `C(n-1, m)` executions fail
  have perR : ∀ R, (if ∃ v, ℓ ∉ A.qry v (R v) then μ.prob R else 0) * ((n - 1).choose m : ℝ) ≤
      ∑ Byz ∈ powersetCard m (univ : Finset (Fin n)),
        ((if Fails A X0 Byz (runOnFlip A X0 ℓ) R then μ.prob R else 0) +
          (if Fails A X1 Byz (runOnFlip A X1 ℓ) R then μ.prob R else 0)) := by
    intro R
    have hite : ∀ (Q : Prop) [Decidable Q],
        (if Q then μ.prob R else 0) = μ.prob R * (if Q then 1 else 0) := by
      intro Q _; split_ifs <;> simp
    split_ifs with hE
    · obtain ⟨v, hv⟩ := hE
      simp_rw [hite, ← mul_add, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (hp R)
      refine choose_le_sum_involution hm v _ _ (fun _ => by split_ifs <;> simp)
        (fun _ => by split_ifs <;> simp) fun Byz hvB => ?_
      rcases claim_3_5 A X0 ℓ Byz R v hvB hv with h | h
      · simp only [h, ↓reduceIte]; split_ifs <;> simp
      · have h' : Fails A X1 (univ \ insert v Byz) (runOnFlip A X1 ℓ) R := h
        simp only [h', ↓reduceIte]; split_ifs <;> simp
    · rw [zero_mul]
      exact Finset.sum_nonneg fun _ _ =>
        add_nonneg (by split_ifs <;> simp [hp R]) (by split_ifs <;> simp [hp R])
  have key : μ.P (fun R => ∃ v, ℓ ∉ A.qry v (R v)) * ((n - 1).choose m : ℝ) ≤
      ∑ Byz ∈ powersetCard m (univ : Finset (Fin n)),
        (μ.P (Fails A X0 Byz (runOnFlip A X0 ℓ)) + μ.P (Fails A X1 Byz (runOnFlip A X1 ℓ))) := by
    simp only [Coins.P]
    rw [Finset.sum_mul]
    simp_rw [← Finset.sum_add_distrib]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun R _ => by convert perR R
  have hBne : (powersetCard m (univ : Finset (Fin n))).Nonempty :=
    powersetCard_nonempty.mpr (by simp; omega)
  have upper : ∑ Byz ∈ powersetCard m (univ : Finset (Fin n)),
      (μ.P (Fails A X0 Byz (runOnFlip A X0 ℓ)) + μ.P (Fails A X1 Byz (runOnFlip A X1 ℓ))) <
      ∑ Byz ∈ powersetCard m (univ : Finset (Fin n)), c / 2 := by
    refine Finset.sum_lt_sum_of_nonempty hBne fun Byz hB => ?_
    have hcard := (mem_powersetCard.mp hB).2
    have h0 := hcon X0 ℓ Byz hcard
    have h1 := hcon X1 ℓ Byz hcard
    linarith
  rw [sum_const, card_powersetCard, card_univ, Fintype.card_fin, nsmul_eq_mul] at upper
  have hchoose : (n.choose m : ℝ) ≤ 2 * ((n - 1).choose m : ℝ) := by
    have : n.choose m ≤ 2 * (n - 1).choose m := by
      rw [hm, show 2 * m + 1 - 1 = 2 * m by omega]; exact choose_le_two_mul m
    exact_mod_cast this
  have hc0 : 0 ≤ c := by
    rw [hc]; linarith [Real.exp_le_one_iff.mpr (show (-1 : ℝ) ≤ 0 by norm_num)]
  have hC0 : (0 : ℝ) ≤ ((n - 1).choose m : ℝ) := Nat.cast_nonneg _
  have h3 : ((n - 1).choose m : ℝ) * c ≤
      ((n - 1).choose m : ℝ) * μ.P (fun R => ∃ v, ℓ ∉ A.qry v (R v)) :=
    mul_le_mul_of_nonneg_left hℓ hC0
  have h4 : (n.choose m : ℝ) * (c / 2) ≤ ((n - 1).choose m : ℝ) * c := by nlinarith
  linarith

/-- **Theorem 3.6, broadcast model.** If honest peers send the same message to everybody, so do
the Byzantine peers of the adversary of `theorem_3_6`. -/
theorem theorem_3_6_broadcast (A : OneRoundAlg n Ω M)
    (hbc : ∀ v ω a u u', A.msg v ω a u = A.msg v ω a u') (X : Fin n → Bool) (ℓ : Fin n) :
    ∀ u ω w w', runOnFlip A X ℓ u ω w = runOnFlip A X ℓ u ω w' :=
  fun u ω w w' => hbc u ω _ w w'

end Podc.ByzantineDownload.LowerBound
