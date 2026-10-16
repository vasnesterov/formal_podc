import Papers.PODC2015.SynchronousCounting.Construction

/-!
# Theorem 1: boosting resilience (§3.5)

`theorem1`: if `A` is a synchronous `c`-counter on `n` nodes with resilience `f` and stabilisation
time `T`, then the construction `B` on `k × n` nodes is a synchronous `C`-counter with resilience
`F` and stabilisation time `T + 3(F+2)(2m)^k`, provided

* `3 ≤ k`, `F < (f+1) m` with `m = ⌈k/2⌉`, `3(F+2)(2m)^k ∣ c` (as in the paper),
* `2f < n` (the paper uses `f < n/3`, justified by the impossibility of counting for `n ≤ 3f`),
* `3F < kn` (the paper claims that this follows from the other assumptions; it does not when
  `n = 1`, see `Counterexample.lean`).
-/

namespace SynchronousCounting

open Podc.SyncCounting Finset

variable {X : Type*} {n f c T k F C : ℕ}

/-- The faulty nodes of block `i`. -/
def blockFaulty (Fa : Finset (Fin k × Fin n)) (i : Fin k) : Finset (Fin n) :=
  univ.filter fun j => (i, j) ∈ Fa

lemma mem_blockFaulty {Fa : Finset (Fin k × Fin n)} {i : Fin k} {j : Fin n} :
    j ∈ blockFaulty Fa i ↔ (i, j) ∈ Fa := by
  simp [blockFaulty]

lemma card_eq_sum_blockFaulty (Fa : Finset (Fin k × Fin n)) :
    Fa.card = ∑ i, (blockFaulty Fa i).card := by
  classical
  have h1 : Fa.card = (univ.filter fun p => p ∈ Fa).card := by
    rw [filter_mem_eq_inter, univ_inter]
  rw [h1, card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [blockFaulty, card_filter]

/-- Fewer than `m` blocks are faulty (have more than `f` faulty nodes) when `|Fa| < (f+1)m`. -/
lemma card_bad_lt (Fa : Finset (Fin k × Fin n)) {m : ℕ} (h : Fa.card < (f + 1) * m) :
    (univ.filter fun i => f < (blockFaulty Fa i).card).card < m := by
  have h1 : (univ.filter fun i => f < (blockFaulty Fa i).card).card * (f + 1) ≤ Fa.card := by
    rw [card_eq_sum_blockFaulty, ← smul_eq_mul, ← sum_const]
    calc ∑ _i ∈ univ.filter fun i => f < (blockFaulty Fa i).card, (f + 1)
        ≤ ∑ i ∈ univ.filter fun i => f < (blockFaulty Fa i).card, (blockFaulty Fa i).card :=
          sum_le_sum fun i hi => (mem_filter.1 hi).2
      _ ≤ ∑ i, (blockFaulty Fa i).card := sum_le_sum_of_subset (filter_subset _ _)
  by_contra hc
  push Not at hc
  have := Nat.mul_le_mul_right (f + 1) hc
  nlinarith

/-- Iterating `incr`. -/
lemma incr_iter_val {C : ℕ} (y : Fin C) (r : ℕ) : ((incr^[r] y : Fin C) : ℕ) = (y + r) % C := by
  induction r with
  | zero => simp [Nat.mod_eq_of_lt y.isLt]
  | succ r ih =>
    rw [Function.iterate_succ_apply', incr]
    simp only [ih, Nat.mod_add_mod, Nat.add_assoc]

variable [NeZero C]

/-- A block of `B` runs a copy of `A`: the projection of an execution of `B` to the base
states of block `i` is an execution of `A` with the faulty nodes of the block. -/
lemma isExec_block (A : Algorithm (Fin n) X c) {Fa : Finset (Fin k × Fin n)}
    {x : ℕ → Fin k × Fin n → BState X C} (hx : IsExec (construction k F C A) Fa x) (i : Fin k) :
    IsExec A (blockFaulty Fa i) (fun t j => (x t (i, j)).1) := by
  intro t j hj
  obtain ⟨m, hm, hstep⟩ := hx t (i, j) (by rwa [mem_blockFaulty] at hj)
  refine ⟨fun j' => (m (i, j')).1, fun j' hj' => ?_, ?_⟩
  · exact congrArg Prod.fst (hm (i, j') (by rwa [mem_blockFaulty] at hj'))
  · simp only [hstep]; rfl

/-- **Theorem 1** (Lenzen–Rybicki–Suomela, PODC 2015), for the construction `B`, with the two
extra hypotheses `2f < n` and `3F < kn` (see the module docstring). -/
theorem theorem1 (A : Algorithm (Fin n) X c) (hA : IsCounter A f T) (hk : 3 ≤ k)
    (hF : F < (f + 1) * half k) (hc : boostTime k F ∣ c) (hn : 2 * f < n)
    (hN : 3 * F < k * n) :
    IsCounter (construction k F C A) F (T + boostTime k F) := by
  intro Fa hFa x hx
  -- parameters
  set m := half k with hm_def
  set τ := tau F with hτ_def
  have hm_eq : m = (k + 1) / 2 := rfl
  have hτ_eq : τ = 3 * (F + 2) := rfl
  have hm : 0 < m := by omega
  have hmk : m ≤ k := by omega
  have hτ : 0 < τ := by omega
  have hn0 : 0 < n := by omega
  have hkn : 3 ≤ k * n := le_trans hk (Nat.le_mul_of_pos_right k hn0)
  have hcardV : Fintype.card (Fin k × Fin n) = k * n := by simp
  have hdvd : ∀ i : ℕ, i < k → τ * (2 * m) ^ (i + 1) ∣ c := fun i hi =>
    (Nat.mul_dvd_mul_left τ (pow_dvd_pow _ hi)).trans hc
  have hτc : τ ∣ c := (Dvd.intro _ rfl).trans (hdvd 0 (by omega))
  -- Step 1: the blocks with at most `f` faulty nodes stabilise (Theorem 1's hypothesis on `A`)
  have hstab : ∀ i : Fin k, ∃ s : ℕ, (blockFaulty Fa i).card ≤ f →
      ∀ r, ∀ j, (i, j) ∉ Fa → (A.h j (x (T + r) (i, j)).1 : ℕ) = (s + r) % c := by
    intro i
    by_cases hg : (blockFaulty Fa i).card ≤ f
    · obtain ⟨v, hv⟩ := hA _ hg _ (isExec_block A hx i)
      exact ⟨v, fun _ r j hj => hv r j (by rwa [mem_blockFaulty])⟩
    · exact ⟨0, fun h => absurd h hg⟩
  choose s hs using hstab
  -- faulty blocks
  set bad := univ.filter fun i : Fin k => f < (blockFaulty Fa i).card with hbad_def
  have hbad : bad.card < m := card_bad_lt Fa (by omega)
  have hbad2 : 2 * bad.card < k := by omega
  have hgood : ∀ i ∉ bad, (blockFaulty Fa i).card ≤ f := by
    intro i hi; simpa [hbad_def] using hi
  have hblk : ∀ i ∉ bad, 2 * (univ.filter fun j => (i, j) ∈ Fa).card < n := by
    intro i hi; have := hgood i hi; unfold blockFaulty at this; omega
  -- a non-faulty block among the first `m`
  obtain ⟨β, hβm, hβ⟩ : ∃ β : Fin k, β.val < m ∧ β ∉ bad := by
    by_contra hcon
    push Not at hcon
    have : (univ : Finset (Fin m)).map (Fin.castLEEmb hmk) ⊆ bad := by
      intro i hi
      obtain ⟨j, -, rfl⟩ := mem_map.1 hi
      exact hcon _ (by simp)
    have := card_le_card this
    simp at this
    omega
  -- Step 2 (Lemma 2): a window of `τ` rounds where all non-faulty blocks point to `β`
  set s' : ℕ → ℕ := fun i => if h : i < k then s ⟨i, h⟩ else 0 with hs'
  obtain ⟨u, -, hu, hwin⟩ := lemma2 hτ hm hβm s' (k - 1) 0
  rw [show k - 1 + 1 = k by omega, zero_add] at hu
  -- Step 3 (Lemma 3): in the window every correct node computes `R = (s β + q) mod τ`
  have hR : ∀ q, u ≤ q → q < u + τ → ∀ v, ∀ msg : Fin k × Fin n → BState X C,
      (∀ w ∉ Fa, msg w = x (T + q) w) → Rval k F C A msg v = (s β + q) % τ := by
    intro q hq1 hq2 v msg hmsg
    apply Rval_eq A msg v Fa bad hbad2 hblk β hβ
    · intro i hi j hj
      have hcv : cval k C A msg i j = (s i + q) % c := by
        unfold cval; rw [hmsg _ hj]; exact hs i (hgood i hi) q j hj
      rw [hcv, ptr_eq (hdvd i i.isLt)]
      have := hwin i (by omega) q hq1 hq2
      simpa [hs', Nat.add_comm] using this
    · intro j hj
      unfold cval rnd
      rw [hmsg _ hj, hs β (hgood β hβ) q j hj, Nat.mod_mod_of_dvd _ hτc]
  -- the phase-king registers
  set a : ℕ → Fin k × Fin n → Option (Fin C) := fun t v => (x t v).2.1 with ha
  set d : ℕ → Fin k × Fin n → Bool := fun t v => (x t v).2.2 with hd
  have hstepAll : ∀ t, ∀ v ∉ Fa, ∃ msg : Fin k × Fin n → BState X C,
      (∀ w ∉ Fa, msg w = x t w) ∧
      (a (t + 1) v, d (t + 1) v) = pkStep F (kingNode k v (Rval k F C A msg v / 3))
        (Rval k F C A msg v) (fun w => (msg w).2.1) (a t v) (d t v) := by
    intro t v hv
    obtain ⟨msg, hmsg, hstep⟩ := hx t v hv
    refine ⟨msg, hmsg, ?_⟩
    simp only [ha, hd, hstep, construction, hmsg v hv]
  -- a fixed node to name the kings
  set v₀ : Fin k × Fin n := (β, ⟨0, hn0⟩)
  set K : ℕ → Fin k × Fin n := fun ℓ => kingNode k v₀ ℓ with hK
  have hstepWin : ∀ q, u ≤ q → q < u + τ →
      PKStep Fa F (K ((s β + q) % τ / 3)) ((s β + q) % τ) (a (T + q)) (d (T + q))
        (a (T + q + 1)) (d (T + q + 1)) := by
    intro q hq1 hq2 v hv
    obtain ⟨msg, hmsg, he⟩ := hstepAll (T + q) v hv
    refine ⟨fun w => (msg w).2.1, fun w hw => by simp [ha, hmsg w hw], ?_⟩
    rw [he, hR q hq1 hq2 v msg hmsg, hK]
    have := Nat.mod_lt (s β + q) hτ
    rw [kingNode_eq v v₀ (by omega)]
  -- Step 4: a correct king whose three instruction sets all fall into the window
  have hmodq : ∀ Q r, r < τ → (τ * Q + r) % τ = r := fun Q r h => by
    rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]
  set S := (range (F + 2)).filter fun ℓ => K ℓ ∉ Fa with hS
  have hS2 : 1 < S.card := by
    have h1 := card_filter_add_card_filter_not (s := range (F + 2)) (fun ℓ => K ℓ ∉ Fa)
    have h2 : ((range (F + 2)).filter fun ℓ => ¬ K ℓ ∉ Fa).card ≤ Fa.card := by
      apply card_le_card_of_injOn K
      · intro ℓ hℓ; simpa using (mem_filter.1 hℓ).2
      · intro ℓ hℓ ℓ' hℓ' he
        have := (mem_filter.1 hℓ).1; have := (mem_filter.1 hℓ').1
        simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at *
        exact kingNode_injective v₀ (by omega) (by omega) he
    rw [card_range, ← hS] at h1
    omega
  set ρ := (s β + u) % τ with hρ
  have hQ := Nat.div_add_mod (s β + u) τ
  have hρτ : ρ < τ := Nat.mod_lt _ hτ
  obtain ⟨ℓ, hℓS, hℓρ⟩ := exists_mem_ne hS2 (ρ / 3)
  obtain ⟨hℓF, hℓK⟩ : ℓ < F + 2 ∧ K ℓ ∉ Fa := by simpa [hS] using hℓS
  obtain ⟨q₀, hq₀u, hq₀τ, hq₀R⟩ : ∃ q₀, u ≤ q₀ ∧ q₀ + 2 < u + τ ∧
      ∀ i < 3, (s β + (q₀ + i)) % τ = 3 * ℓ + i := by
    by_cases hle : ρ ≤ 3 * ℓ
    · refine ⟨u + (3 * ℓ - ρ), by omega, by omega, fun i hi => ?_⟩
      rw [show s β + (u + (3 * ℓ - ρ) + i) = τ * ((s β + u) / τ) + (3 * ℓ + i) by omega]
      exact hmodq _ _ (by omega)
    · have : ρ / 3 > ℓ := by omega
      refine ⟨u + τ + 3 * ℓ - ρ, by omega, by omega, fun i hi => ?_⟩
      rw [show s β + (u + τ + 3 * ℓ - ρ + i) = τ * ((s β + u) / τ + 1) + (3 * ℓ + i) by
        rw [Nat.mul_add_one]; omega]
      exact hmodq _ _ (by omega)
  have h₀ := hstepWin q₀ hq₀u (by omega)
  have h₁ := hstepWin (q₀ + 1) (by omega) (by omega)
  have h₂ := hstepWin (q₀ + 2) (by omega) (by omega)
  rw [show q₀ = q₀ + 0 from rfl, hq₀R 0 (by norm_num)] at h₀
  rw [hq₀R 1 (by norm_num), show T + (q₀ + 1) = T + q₀ + 1 by omega] at h₁
  rw [hq₀R 2 (by norm_num), show T + (q₀ + 2) = T + q₀ + 1 + 1 by omega,
    show (3 * ℓ + 2) / 3 = ℓ by omega] at h₂
  -- Lemma 4: agreement
  obtain ⟨y, hy⟩ := lemma4 Fa hFa (by rw [hcardV]; exact hN) hℓK (r := 3 * ℓ) (by omega)
    (by simpa using h₀) h₁ h₂
  -- Lemma 5: agreement persists
  have hpers : ∀ r, ∀ v ∉ Fa,
      a (T + q₀ + 1 + 1 + 1 + r) v = some (incr^[r] y) ∧ d (T + q₀ + 1 + 1 + 1 + r) v = true := by
    intro r
    induction r with
    | zero => simpa using hy
    | succ r ih =>
      intro v hv
      obtain ⟨msg, hmsg, he⟩ := hstepAll (T + q₀ + 1 + 1 + 1 + r) v hv
      rw [(ih v hv).1, (ih v hv).2, lemma5 Fa hFa (by rw [hcardV]; omega) _ _ _ (incr^[r] y)
        (fun w hw => by rw [hmsg w hw]; exact (ih w hw).1)] at he
      simp only [Prod.mk.injEq] at he
      rw [Function.iterate_succ_apply']
      exact ⟨he.1, he.2⟩
  -- conclusion
  have hT : T + q₀ + 1 + 1 + 1 ≤ T + boostTime k F := by
    have : boostTime k F = τ * (2 * m) ^ k := rfl
    omega
  refine ⟨y + (T + boostTime k F - (T + q₀ + 1 + 1 + 1)), fun r v hv => ?_⟩
  have := (hpers (T + boostTime k F - (T + q₀ + 1 + 1 + 1) + r) v hv).1
  rw [show T + q₀ + 1 + 1 + 1 + (T + boostTime k F - (T + q₀ + 1 + 1 + 1) + r) =
    T + boostTime k F + r by omega] at this
  simp only [construction]
  rw [show (x (T + boostTime k F + r) v).2.1 = a (T + boostTime k F + r) v from rfl, this,
    Option.getD_some, incr_iter_val]
  congr 1; omega

end SynchronousCounting
