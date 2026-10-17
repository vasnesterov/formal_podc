import Papers.PODC2023.LeaderTradeoffs.MessageLB
import Papers.PODC2023.LeaderTradeoffs.SingleSend

/-!
# Theorem 3.11: `Ω(n log n)` messages for every time-bounded algorithm

* `Level A U i R N M` (Lemma 3.14): `N` pairwise disjoint `2^i`-subsets of `U`, each running in
  isolation through round `R` with capacity `2^(i-1) - 1` and at least `M` messages.
* `level_step`: from `2 T N'` sets at level `i` to `N'` sets at level `i + 1` (pigeonhole on the
  stop round, then pairing and `merge`).
* `single_send_lower_bound` (Lemma 3.13): with `n = 2^k`, `k ≥ 2`, and an ID universe of size
  `≥ n log₂ n + n T^(log₂ n - 1)`, a single-send algorithm electing within `T` rounds sends at
  least `(n/2) log₂ n` messages in some execution.
* `theorem_3_11`: the same for arbitrary (multicast) algorithms, through the simulation of
  Lemma 3.12 (time `n T`), with an ID universe of size `≥ n log₂ n + n^(log₂ n) T^(log₂ n - 1)`.
  The paper states `n^(log₂ n) T^(log₂ n - 1)`; its proof (Lemma 3.14 assumes
  `n T^(log₂ n - 1) + n log₂ n` IDs for the single-send algorithm with time `n T`) needs the
  extra `n log₂ n` IDs removed by Corollary 3.7.
-/

open Classical Finset Function

namespace LeaderTradeoffs

variable {m : ℕ}

/-- The message count guaranteed at level `i`: `M_0 = 0`, `M_{i+1} = 2 (M_i + h_i)` with
`h_i = max(1, 2^(i-1))` new messages per set and phase. -/
def lbMsgs : ℕ → ℕ
  | 0 => 0
  | i + 1 => 2 * (lbMsgs i + (2 ^ i / 2 - 1) + 1)

theorem lbMsgs_succ (i : ℕ) (hi : 1 ≤ i) :
    lbMsgs (i + 1) = 2 * lbMsgs i + 2 ^ i := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  show 2 * (lbMsgs (j + 1) + (2 ^ (j + 1) / 2 - 1) + 1) = _
  have h2 : 2 ^ (j + 1) / 2 = 2 ^ j := by rw [pow_succ]; simp
  have h3 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  rw [h2, pow_succ]
  omega

theorem two_mul_lbMsgs (i : ℕ) (hi : 1 ≤ i) : 2 * lbMsgs i = (i + 1) * 2 ^ i := by
  induction i with
  | zero => omega
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rfl
    · rw [lbMsgs_succ i hpos, pow_succ]
      have := ih hpos
      nlinarith

/-- The data of level `i` of Lemma 3.14. -/
def Level (A : Algorithm m) (U : Finset ℕ) (i R N M : ℕ) : Prop :=
  ∃ (X : Fin N → Finset ℕ) (q : Fin N → PortMap m), Pairwise (Disjoint on X) ∧
    (∀ a, X a ⊆ U) ∧ (∀ a, (X a).card = 2 ^ i) ∧ (∀ a, WF (q a) (X a)) ∧
    (∀ a, Valid A (q a) R (X a)) ∧
    (∀ a, ∀ u ∈ X a, 2 ^ i / 2 - 1 ≤ (nonNbrs (q a) (X a) u).card) ∧
    (∀ a, M ≤ msgs A (q a) R (X a))

theorem level_zero (A : Algorithm m) (U : Finset ℕ) : Level A U 0 0 U.card 0 := by
  let e := U.equivFin.symm
  refine ⟨fun a => {(e a).1}, fun _ _ _ => none, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    simp only [onFun, Finset.disjoint_singleton]
    intro h
    exact hab (e.injective (Subtype.ext h))
  · intro a; simp [(e a).2]
  · intro a; simp
  · intro a; exact ⟨by simp, by simp, by simp, by simp⟩
  · intro a r' hr'; omega
  · intro a u _; simp
  · intro a; exact Nat.zero_le _

theorem level_mono {A : Algorithm m} {U : Finset ℕ} {i R N N' M : ℕ} (h : N' ≤ N)
    (hL : Level A U i R N M) : Level A U i R N' M := by
  obtain ⟨X, q, hd, h1, h2, h3, h4, h5, h6⟩ := hL
  refine ⟨fun a => X (Fin.castLE h a), fun a => q (Fin.castLE h a), ?_, fun a => h1 _,
    fun a => h2 _, fun a => h3 _, fun a => h4 _, fun a => h5 _, fun a => h6 _⟩
  intro a b hab
  exact hd (fun e => hab (Fin.castLE_injective h e))

/-- One level of Lemma 3.14. -/
theorem level_step {A : Algorithm m} (hS : ∀ s, sendCount A s ≤ 1) {U : Finset ℕ}
    {i R T N N' M : ℕ} (hT : 1 ≤ T) (hno : ∀ X ⊆ U, X.card = 2 ^ i → ¬ Isolable A T X)
    (hi : 2 ^ (i + 1) ≤ m + 1) (hRT : R ≤ T) (hN : 2 * T * N' ≤ N)
    (hL : Level A U i R N M) :
    ∃ R', R' ≤ T ∧ Level A U (i + 1) R' N' (2 * (M + (2 ^ i / 2 - 1) + 1)) := by
  obtain ⟨X, q, hd, hsub, hcard, hwf, hval, hcap, hM⟩ := hL
  have hXm : ∀ a, (X a).card ≤ m + 1 := fun a => by
    rw [hcard a]; exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) hi
  have hab : ∀ a, ∃ ρ, R ≤ ρ ∧ ρ < T ∧ ∃ q' : PortMap m, WF q' (X a) ∧ Valid A q' ρ (X a) ∧
      M + (2 ^ i / 2 - 1) + 1 ≤ msgs A q' (ρ + 1) (X a) := fun a =>
    absorb hS (hXm a) (hno _ (hsub a) (hcard a)) hRT (hwf a) (hval a) (hcap a) (hM a)
  choose ρ hρ1 hρ2 q' hq'wf hq'val hq'M using hab
  -- pigeonhole on the stop round
  obtain ⟨ρ0, hρ0, hfib⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := (univ : Finset (Fin N))) (t := range T) (f := ρ) (n := 2 * N')
    (fun a _ => Finset.mem_range.2 (hρ2 a)) ⟨0, Finset.mem_range.2 (by omega)⟩
    (by rw [Finset.card_range, Finset.card_univ, Fintype.card_fin]; linarith)
  obtain ⟨e, he, heF⟩ := exists_fin_embedding _ (2 * N') hfib
  have heρ : ∀ b, ρ (e b) = ρ0 := fun b => (Finset.mem_filter.1 (heF b)).2
  let a1 : Fin N' → Fin N := fun j => e ⟨2 * j, by omega⟩
  let a2 : Fin N' → Fin N := fun j => e ⟨2 * j + 1, by omega⟩
  have ha12 : ∀ j, a1 j ≠ a2 j := fun j h => by
    have := he h
    simp only [Fin.mk.injEq] at this
    omega
  have hmerge : ∀ j, ∃ qq : PortMap m, WF qq (X (a1 j) ∪ X (a2 j)) ∧
      Valid A qq (ρ0 + 1) (X (a1 j) ∪ X (a2 j)) ∧
      msgs A qq (ρ0 + 1) (X (a1 j) ∪ X (a2 j)) =
        msgs A (q' (a1 j)) (ρ0 + 1) (X (a1 j)) + msgs A (q' (a2 j)) (ρ0 + 1) (X (a2 j)) ∧
      ∀ u ∈ X (a1 j) ∪ X (a2 j), 2 ^ i - 1 ≤ (nonNbrs qq (X (a1 j) ∪ X (a2 j)) u).card := by
    intro j
    have hv1 := hq'val (a1 j)
    have hv2 := hq'val (a2 j)
    rw [heρ] at hv1 hv2
    exact merge hS (hd (ha12 j)) (hcard _) (hcard _)
      (by rw [← two_mul, ← pow_succ']; exact hi) (hq'wf _) hv1 (hq'wf _) hv2
  choose qq hqqwf hqqval hqqM hqqcap using hmerge
  refine ⟨ρ0 + 1, by have := Finset.mem_range.1 hρ0; omega,
    fun j => X (a1 j) ∪ X (a2 j), qq, ?_, ?_, ?_, hqqwf, hqqval, ?_, ?_⟩
  · intro j j' hjj
    have hne : ∀ x y : Fin (2 * N'), x.1 ≠ y.1 → e x ≠ e y := fun x y hxy h =>
      hxy (by rw [he h])
    have hjv : (j : ℕ) ≠ j' := fun h => hjj (Fin.ext h)
    simp only [onFun, Finset.disjoint_union_left, Finset.disjoint_union_right]
    refine ⟨⟨hd (hne _ _ ?_), hd (hne _ _ ?_)⟩, ⟨hd (hne _ _ ?_), hd (hne _ _ ?_)⟩⟩ <;>
      simp only <;> omega
  · intro j; exact Finset.union_subset (hsub _) (hsub _)
  · intro j
    rw [Finset.card_union_of_disjoint (hd (ha12 j)), hcard, hcard, pow_succ]
    ring
  · intro j u hu
    have := hqqcap j u hu
    rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
    exact this
  · intro j
    rw [hqqM j]
    have h1 := hq'M (a1 j)
    have h2 := hq'M (a2 j)
    rw [heρ] at h1 h2
    omega

theorem msgs_biUnion {ι : Type*} [Fintype ι] (A : Algorithm m) (p : PortMap m) (T : ℕ)
    (X : ι → Finset ℕ) (hd : Pairwise (Disjoint on X)) :
    msgs A p T (univ.biUnion X) = ∑ a, msgs A p T (X a) := by
  simp only [msgs, roundMsgs]
  calc ∑ r ∈ range T, ∑ u ∈ univ.biUnion X, sendCount A (run A p r u)
      = ∑ r ∈ range T, ∑ a, ∑ u ∈ X a, sendCount A (run A p r u) :=
        Finset.sum_congr rfl fun r _ => Finset.sum_biUnion (fun a _ b _ hab => hd hab)
    _ = _ := Finset.sum_comm

/-- **Lemma 3.13** (single-send algorithms). Let `n = m + 1 = 2^k` with `k ≥ 2`, and let a
single-send algorithm elect a leader within `T` rounds for all ID assignments from `U`, where
`|U| ≥ n log₂ n + n T^(log₂ n - 1)`. Then some execution sends at least `(n/2) log₂ n`
messages. -/
theorem single_send_lower_bound {A : Algorithm m} (hS : ∀ s, sendCount A s ≤ 1) {k T : ℕ}
    (hk : m + 1 = 2 ^ k) (hk2 : 2 ≤ k) {U : Finset ℕ}
    (hU : k * (m + 1) + (m + 1) * T ^ (k - 1) ≤ U.card) (hA : ElectsBy A U T) :
    ∃ I ⊆ U, I.card = m + 1 ∧ ∃ P : PortMap m, IsPortMap P I ∧
      k * 2 ^ (k - 1) ≤ msgs A P T I := by
  have hn2 : 2 ≤ m + 1 := by
    rw [hk]; calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  -- `T ≥ 1`: at time `0` all singletons are isolated
  have hT : 1 ≤ T := by
    by_contra h0
    have hT0 : T = 0 := by omega
    have hUc : m + 2 ≤ U.card := by
      have : 2 * (m + 1) ≤ k * (m + 1) := Nat.mul_le_mul_right _ hk2
      omega
    obtain ⟨e, he, heU⟩ := exists_fin_embedding U (m + 1 + 1) hUc
    exact not_disjoint_isolable hA (s := 1) (N := m + 1) (by ring) hn2 (fun a => {e a})
      (fun a b hab => by
        simp only [onFun, Finset.disjoint_singleton]
        exact fun h => hab (he h))
      (fun a => by simp [heU a]) (fun a => by simp)
      (fun a => ⟨fun _ _ => none, ⟨by simp, by simp, by simp, by simp⟩,
        fun r' hr' => by omega⟩)
  obtain ⟨U₀, hU₀, hc₀, hno⟩ := exists_universe_no_isolable_pow hA hk
  have hpow : (m + 1) * T ^ (k - 1) = 2 * (2 * T) ^ (k - 1) := by
    rw [hk, mul_pow, ← mul_assoc, ← pow_succ']
    congr 2
    omega
  have hiter : ∀ i ≤ k - 1, ∃ R ≤ T,
      Level A U₀ i R (2 * (2 * T) ^ (k - 1 - i)) (lbMsgs i) := by
    intro i
    induction i with
    | zero =>
      intro _
      refine ⟨0, Nat.zero_le _, level_mono ?_ (level_zero A U₀)⟩
      rw [Nat.sub_zero, ← hpow]
      omega
    | succ i ih =>
      intro hi
      obtain ⟨R, hR, hL⟩ := ih (by omega)
      obtain ⟨R', hR', hL'⟩ := level_step hS hT
        (fun X hX hXc => hno i (by omega) X hX hXc)
        (by rw [hk]; exact Nat.pow_le_pow_right (by norm_num) (by omega)) hR
        (N' := 2 * (2 * T) ^ (k - 1 - (i + 1)))
        (by
          rw [show k - 1 - i = (k - 1 - (i + 1)) + 1 by omega, pow_succ]
          ring_nf
          exact le_rfl) hL
      exact ⟨R', hR', hL'⟩
  obtain ⟨R, hRT, hL⟩ := hiter (k - 1) le_rfl
  rw [Nat.sub_self, pow_zero, mul_one] at hL
  obtain ⟨X, q, hd, hsub, hcard, hwf, hval, -, hM⟩ := hL
  have hJ : (univ.biUnion X).card = m + 1 := by
    rw [card_biUnion_univ X hd _ hcard, Fintype.card_fin, hk, ← pow_succ']
    congr 1
    omega
  obtain ⟨P, hP, hrun⟩ := glue_full A X q hd hwf R hval hJ
  refine ⟨univ.biUnion X, ?_, hJ, P, hP, ?_⟩
  · intro u hu
    obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 hu
    exact hU₀ (hsub a ha)
  · have h1 : msgs A P R (univ.biUnion X) = ∑ a, msgs A (q a) R (X a) := by
      rw [msgs_biUnion A P R X hd]
      refine Finset.sum_congr rfl fun a _ => ?_
      exact msgs_congr fun r' hr' u hu => hrun a u hu r' hr'.le
    have h2 : ∑ a : Fin 2, msgs A (q a) R (X a) ≥ 2 * lbMsgs (k - 1) := by
      rw [Fin.sum_univ_two]
      have := hM 0
      have := hM 1
      omega
    have h3 := two_mul_lbMsgs (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at h3
    have h4 := msgs_mono (A := A) (p := P) (S := univ.biUnion X) hRT
    omega

/-- **Theorem 3.11.** Let `n = m + 1 = 2^k` with `k ≥ 2`, and let a deterministic algorithm
elect a leader within `T` rounds for all ID assignments from a universe `U` with
`|U| ≥ n log₂ n + n^(log₂ n) T^(log₂ n - 1)`. Then some execution (ID assignment from `U` and
port map) sends at least `(n/2) log₂ n` messages within the first `T` rounds. -/
theorem theorem_3_11 {A : Algorithm m} {k T : ℕ} (hk : m + 1 = 2 ^ k) (hk2 : 2 ≤ k)
    {U : Finset ℕ} (hU : k * (m + 1) + (m + 1) ^ k * T ^ (k - 1) ≤ U.card)
    (hA : ElectsBy A U T) :
    ∃ I ⊆ U, I.card = m + 1 ∧ ∃ P : PortMap m, IsPortMap P I ∧
      k * 2 ^ (k - 1) ≤ msgs A P T I := by
  have hU' : k * (m + 1) + (m + 1) * ((m + 1) * T) ^ (k - 1) ≤ U.card := by
    have : (m + 1) * ((m + 1) * T) ^ (k - 1) = (m + 1) ^ k * T ^ (k - 1) := by
      rw [mul_pow, ← mul_assoc, ← pow_succ']
      congr 2
      omega
    rw [this]; exact hU
  obtain ⟨I, hIU, hIc, P, hP, hmsgs⟩ :=
    single_send_lower_bound (simulate_singleSend A) hk hk2 hU' (electsBy_simulate hA)
  exact ⟨I, hIU, hIc, P, hP, by rw [← msgs_simulate]; exact hmsgs⟩

end LeaderTradeoffs
