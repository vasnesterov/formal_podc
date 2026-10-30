import Papers.PODC2022.BindingCrusaderAgreement.Basic

/-!
# The agreement framework (Algorithms 1 and 2): deterministic core

Abraham, Ben-David, Yandamuri, PODC 2022, Section 3: Algorithm 1 (rounds of BCA followed by a
strong common coin; Theorems 3.1, 3.3, Lemma 3.2) and Algorithm 2 (rounds of graded BCA followed
by an `ε`-good coin; Theorems 3.4, 3.5).

We reason at the level of BCA instances, as the paper's proofs do. A run records, for every round
`r` (`r = 0` is the paper's first round):
* `Start r`: the parties that start round `r` (with BCA input `est r p`);
* `Dec r ⊆ Start r`: the parties whose BCA instance of round `r` returned (`val r p`);
* the coin value(s) of round `r`.
A party starting round `r + 1` has finished round `r`, and its next input is computed by lines 6–8
of Algorithm 1 (lines 5–6 of Algorithm 2). The BCA instance of each round is assumed to satisfy
agreement and validity among its participants (hypotheses `BCA`/`GBCA`).

The same statements cover the Byzantine version (`Start r = Dec r = H`, the non-faulty parties,
strong validity) and the crash version (`Start r`, `Dec r` = all parties that start/finish the
round, crashed ones included; weak validity "if all participants have input `v`").

## Main results
* `Alg1.lemma_3_2`, `Alg1.agreement`, `Alg1.validity` (agreement and validity parts of
  Theorems 3.1 and 3.3);
* `Alg1.binding_step`: if the coin of round `r` equals the value `b` the adversary is bound to,
  all parties start round `r + 1` with `b` (the deterministic step of the termination proof),
  and `Alg1.commit_after_binding`: they all commit `b` in every later round whose coin is `b`;
* `Alg2.agreement`, `Alg2.validity`, `Alg2.binding_step` (Theorems 3.4 and 3.5).

The probabilistic part (expected number of rounds, unpredictability of the coin) is not
formalized.
-/

namespace Podc.BindingCrusaderAgreement

/-! ## Algorithm 1 -/

namespace Alg1

/-- A run of Algorithm 1 at the level of BCA instances and a strong coin `coin r`. -/
structure Run (P : Type*) where
  /-- Parties starting round `r`. -/
  Start : ℕ → Set P
  /-- Parties whose BCA of round `r` returned. -/
  Dec : ℕ → Set P
  /-- BCA input of round `r`. -/
  est : ℕ → P → Bool
  /-- BCA output of round `r` (`none` = `⊥`). -/
  val : ℕ → P → Option Bool
  /-- The strong coin of round `r` (the same for all parties). -/
  coin : ℕ → Bool
  dec_sub : ∀ r, Dec r ⊆ Start r
  start_succ : ∀ r, Start (r + 1) ⊆ Dec r
  /-- Lines 6–8: keep a non-`⊥` BCA output, otherwise adopt the coin. -/
  est_succ : ∀ r p, p ∈ Start (r + 1) → est (r + 1) p = (val r p).getD (coin r)

variable {P : Type*} (R : Run P)

/-- Line 6: `p` commits `v` in round `r`. -/
def Run.Commits (r : ℕ) (p : P) (v : Bool) : Prop :=
  p ∈ R.Dec r ∧ R.val r p = some v ∧ R.coin r = v

/-- Agreement and validity of the BCA instance of every round (Definition 3.1; for crash
faults, weak validity among the participants). -/
structure Run.BCA : Prop where
  agree : ∀ r p q a b, p ∈ R.Dec r → q ∈ R.Dec r → R.val r p = some a → R.val r q = some b →
    a = b
  valid : ∀ r v, (∀ p ∈ R.Start r, R.est r p = v) → ∀ p ∈ R.Dec r, R.val r p = some v

variable {R}

/-- Lemma 3.2: if all parties start round `r` with estimate `v`, they keep `v` and their BCA
returns `v` in every later round; hence they commit `v` in every round whose coin is `v`. -/
theorem lemma_3_2 (hR : R.BCA) {r : ℕ} {v : Bool} (hv : ∀ p ∈ R.Start r, R.est r p = v) :
    ∀ r', r ≤ r' → (∀ p ∈ R.Start r', R.est r' p = v) ∧ ∀ p ∈ R.Dec r', R.val r' p = some v := by
  intro r' hr'
  induction hr' with
  | refl => exact ⟨hv, hR.valid r v hv⟩
  | step _ ih =>
    rename_i m _
    have hest : ∀ p ∈ R.Start (m + 1), R.est (m + 1) p = v := fun p hp => by
      rw [R.est_succ m p hp, ih.2 p (R.start_succ m hp)]
      rfl
    exact ⟨hest, hR.valid _ v hest⟩

/-- After a commit of `v` in round `r`, all parties start round `r + 1` with estimate `v`. -/
theorem est_succ_of_commits (hR : R.BCA) {r : ℕ} {p : P} {v : Bool} (hp : R.Commits r p v) :
    ∀ q ∈ R.Start (r + 1), R.est (r + 1) q = v := by
  intro q hq
  rw [R.est_succ r q hq]
  rcases hval : R.val r q with _ | a
  · exact hp.2.2
  · simp only [Option.getD_some]
    exact hR.agree r q p a v (R.start_succ r hq) hp.1 hval hp.2.1

/-- Agreement of Theorems 3.1 and 3.3: any two commits (of any two parties, in any rounds) are
equal. -/
theorem agreement (hR : R.BCA) {r r' : ℕ} {p q : P} {a b : Bool} (hp : R.Commits r p a)
    (hq : R.Commits r' q b) : a = b := by
  wlog hrr : r ≤ r' generalizing r r' p q a b
  · exact (this hq hp (by omega)).symm
  rcases Nat.eq_or_lt_of_le hrr with rfl | hlt
  · exact hp.2.2.symm.trans hq.2.2
  · have := (lemma_3_2 hR (est_succ_of_commits hR hp) r' hlt).2 q hq.1
    rw [hq.2.1] at this
    exact (Option.some.inj this).symm

/-- Validity of Theorems 3.1 and 3.3: if all parties start with `v`, only `v` is committed, and
every party commits `v` in every round whose coin is `v`. -/
theorem validity (hR : R.BCA) {v : Bool} (hv : ∀ p ∈ R.Start 0, R.est 0 p = v) :
    (∀ r p b, R.Commits r p b → b = v) ∧ (∀ r, R.coin r = v → ∀ p ∈ R.Dec r, R.Commits r p v) :=
  ⟨fun r p b hp => by
    have := (lemma_3_2 hR hv r (Nat.zero_le r)).2 p hp.1
    rw [hp.2.1] at this
    exact Option.some.inj this,
   fun r hc p hp => ⟨hp, (lemma_3_2 hR hv r (Nat.zero_le r)).2 p hp, hc⟩⟩

/-- Termination step of Theorem 3.1: if no party's BCA of round `r` returns `1 − b` (binding)
and the coin of round `r` is `b`, all parties start round `r + 1` with estimate `b`. -/
theorem binding_step {r : ℕ} {b : Bool} (hb : ∀ p ∈ R.Dec r, R.val r p ≠ some (!b))
    (hc : R.coin r = b) : ∀ p ∈ R.Start (r + 1), R.est (r + 1) p = b := by
  intro p hp
  rw [R.est_succ r p hp]
  rcases hval : R.val r p with _ | a
  · exact hc
  · simp only [Option.getD_some]
    by_contra hab
    have : a = !b := by cases a <;> cases b <;> simp_all
    exact hb p (R.start_succ r hp) (this ▸ hval)

/-- After a successful round `r` (coin = bound value `b`), every party finishing a later round
whose coin is `b` commits `b` in it. -/
theorem commit_after_binding (hR : R.BCA) {r : ℕ} {b : Bool}
    (hb : ∀ p ∈ R.Dec r, R.val r p ≠ some (!b)) (hc : R.coin r = b) {r' : ℕ} (hr' : r < r')
    (hc' : R.coin r' = b) : ∀ p ∈ R.Dec r', R.Commits r' p b := fun p hp =>
  ⟨hp, (lemma_3_2 hR (binding_step hb hc) r' hr').2 p hp, hc'⟩

end Alg1

/-! ## Algorithm 2 -/

namespace Alg2

/-- Lines 5–6 of Algorithm 2: the next input. -/
def next (g : Grade) (c : Bool) : Bool :=
  match g with
  | .two v => v
  | .one v => v
  | .zero => c

/-- A run of Algorithm 2 at the level of GBCA instances; the weak coin may give different
values to different parties (`coin r p`). -/
structure Run (P : Type*) where
  /-- Parties starting round `r`. -/
  Start : ℕ → Set P
  /-- Parties whose GBCA of round `r` returned. -/
  Dec : ℕ → Set P
  /-- GBCA input of round `r`. -/
  est : ℕ → P → Bool
  /-- GBCA output of round `r`. -/
  out : ℕ → P → Grade
  /-- The weak coin of round `r` as seen by `p`. -/
  coin : ℕ → P → Bool
  dec_sub : ∀ r, Dec r ⊆ Start r
  start_succ : ∀ r, Start (r + 1) ⊆ Dec r
  est_succ : ∀ r p, p ∈ Start (r + 1) → est (r + 1) p = next (out r p) (coin r p)

variable {P : Type*} (R : Run P)

/-- Line 7: `p` commits `v` in round `r` (its GBCA returned `v` with grade 2). -/
def Run.Commits (r : ℕ) (p : P) (v : Bool) : Prop := p ∈ R.Dec r ∧ R.out r p = .two v

/-- Graded agreement and validity of every GBCA instance (Definition 3.2). -/
structure Run.GBCA : Prop where
  agree : ∀ r p q a b, p ∈ R.Dec r → q ∈ R.Dec r → (R.out r p).HasVal a →
    (R.out r q).HasVal b → a = b
  agree_zero : ∀ r p q a, p ∈ R.Dec r → q ∈ R.Dec r → R.out r p = .two a → R.out r q ≠ .zero
  valid : ∀ r v, (∀ p ∈ R.Start r, R.est r p = v) → ∀ p ∈ R.Dec r, R.out r p = .two v

variable {R}

/-- Analogue of Lemma 3.2 for Algorithm 2. -/
theorem stable (hR : R.GBCA) {r : ℕ} {v : Bool} (hv : ∀ p ∈ R.Start r, R.est r p = v) :
    ∀ r', r ≤ r' → (∀ p ∈ R.Start r', R.est r' p = v) ∧ ∀ p ∈ R.Dec r', R.out r' p = .two v := by
  intro r' hr'
  induction hr' with
  | refl => exact ⟨hv, hR.valid r v hv⟩
  | step _ ih =>
    rename_i m _
    have hest : ∀ p ∈ R.Start (m + 1), R.est (m + 1) p = v := fun p hp => by
      rw [R.est_succ m p hp, ih.2 p (R.start_succ m hp)]
      rfl
    exact ⟨hest, hR.valid _ v hest⟩

/-- After a commit of `v` in round `r`, all parties start round `r + 1` with `v` (graded
agreement: every output of round `r` is `v` with grade `≥ 1`). -/
theorem est_succ_of_commits (hR : R.GBCA) {r : ℕ} {p : P} {v : Bool} (hp : R.Commits r p v) :
    ∀ q ∈ R.Start (r + 1), R.est (r + 1) q = v := by
  intro q hq
  have hqd := R.start_succ r hq
  rw [R.est_succ r q hq]
  have hpv : (R.out r p).HasVal v := Or.inl hp.2
  rcases hout : R.out r q with a | a | _
  · exact hR.agree r q p a v hqd hp.1 (Or.inl hout) hpv
  · exact hR.agree r q p a v hqd hp.1 (Or.inr hout) hpv
  · exact absurd hout (hR.agree_zero r p q v hp.1 hqd hp.2)

/-- Agreement of Theorems 3.4 and 3.5. -/
theorem agreement (hR : R.GBCA) {r r' : ℕ} {p q : P} {a b : Bool} (hp : R.Commits r p a)
    (hq : R.Commits r' q b) : a = b := by
  wlog hrr : r ≤ r' generalizing r r' p q a b
  · exact (this hq hp (by omega)).symm
  rcases Nat.eq_or_lt_of_le hrr with rfl | hlt
  · exact hR.agree r p q a b hp.1 hq.1 (Or.inl hp.2) (Or.inl hq.2)
  · have := (stable hR (est_succ_of_commits hR hp) r' hlt).2 q hq.1
    rw [hq.2] at this
    exact (Grade.two.inj this).symm

/-- Validity of Theorems 3.4 and 3.5: if all parties start with `v`, every party commits `v` in
every round, and nothing else is committed. -/
theorem validity (hR : R.GBCA) {v : Bool} (hv : ∀ p ∈ R.Start 0, R.est 0 p = v) :
    (∀ r p b, R.Commits r p b → b = v) ∧ (∀ r, ∀ p ∈ R.Dec r, R.Commits r p v) :=
  ⟨fun r p b hp => by
    have := (stable hR hv r (Nat.zero_le r)).2 p hp.1
    rw [hp.2] at this
    exact Grade.two.inj this,
   fun r p hp => ⟨hp, (stable hR hv r (Nat.zero_le r)).2 p hp⟩⟩

/-- Termination step of Theorem 3.4: if no output of round `r` is `1 − b` with grade `≥ 1`
(graded binding) and every party starting round `r + 1` saw coin `b`, all of them start round
`r + 1` with `b` and hence commit `b` in round `r + 1` (and every later round). -/
theorem binding_step (hR : R.GBCA) {r : ℕ} {b : Bool}
    (hb : ∀ p ∈ R.Dec r, ¬ (R.out r p).HasVal (!b)) (hc : ∀ p ∈ R.Start (r + 1), R.coin r p = b) :
    (∀ p ∈ R.Start (r + 1), R.est (r + 1) p = b) ∧
      ∀ r', r < r' → ∀ p ∈ R.Dec r', R.Commits r' p b := by
  have hest : ∀ p ∈ R.Start (r + 1), R.est (r + 1) p = b := by
    intro p hp
    have hpd := R.start_succ r hp
    rw [R.est_succ r p hp]
    rcases hout : R.out r p with a | a | _
    · by_contra hab
      have : a = !b := by cases a <;> cases b <;> simp_all [next]
      exact hb p hpd (Or.inl (this ▸ hout))
    · by_contra hab
      have : a = !b := by cases a <;> cases b <;> simp_all [next]
      exact hb p hpd (Or.inr (this ▸ hout))
    · exact hc p hp
  exact ⟨hest, fun r' hr' p hp => ⟨hp, (stable hR hest r' hr').2 p hp⟩⟩

end Alg2

end Podc.BindingCrusaderAgreement
