import Papers.PODC2021.PPStateComplexity.Leaders
import Podc.Foundations.Combinatorics.DiophantineDecomposition

/-!
# A double-exponential upper bound for leaderless protocols (Section 5)

`C =π⇒ C'` (`C' = C + Δπ`) is the flow equation `Cslib.PopulationProtocol.FlowEq C C' π` of the
multiset model.

* Lemma 5.1(ii) (`lemma_5_1_ii`), in a stronger form: only the pre-states of transitions in the
  support of `π` must carry `2|π|` agents.
* Lemma 5.2 (`lemma_5_2`, with the missing hypothesis `b ≥ 1`).
* Lemmas 5.3, 5.4 (`lemma_5_3`, `lemma_5_4`) for the set of *coverable* states (the paper assumes,
  without saying so, that every state is coverable).
* Corollary 5.7 / Lemma 5.8 (`lemma_5_8`) with the constant `ξ(n) = 4^(2^n - 1)` from our
  weak Pottier theorem `Cslib.exists_small_decomposition` instead of Pottier's
  `ξ = 2(2|T|+1)^|Q|`.
* Theorem 5.9 (`theorem_5_9`): `η ≤ ξ n β 3^n ≤ 2^((2n+2)!)`.
-/

namespace Podc.PPStateComplexity

open Cslib Cslib.PopulationProtocol Finset

variable {Q : Type*} [DecidableEq Q]

theorem Transition.abs_delta_le (t : Transition Q) (q : Q) : |t.delta q| ≤ 2 := by
  have h1 := count_pre_le_two t q
  have h2 : t.post.count q ≤ 2 := (Multiset.count_le_card q _).trans (by simp)
  simp only [Transition.delta, abs_le]
  omega

variable [Fintype Q]

/-- **Lemma 5.1(ii)** (strengthened). If `C =π⇒ C'`, all transitions in the support of `π` belong
to `T`, and every pre-state `q` of such a transition satisfies `C(q) ≥ 2|π|`, then `C →* C'`
(by any sequence with Parikh vector `π`). -/
theorem lemma_5_1_ii {T : Set (Transition Q)} {π : Transition Q → ℕ} {C C' : Multiset Q}
    (hπ : FlowEq C C' π) (hT : ∀ t, π t ≠ 0 → t ∈ T)
    (hsat : ∀ t, π t ≠ 0 → ∀ q ∈ t.pre, 2 * ∑ t, π t ≤ C.count q) : MReach T C C' := by
  induction hN : ∑ t, π t generalizing π C with
  | zero =>
    have h0 : ∀ t, π t = 0 := fun t => (sum_eq_zero_iff.1 hN) t (mem_univ _)
    have : C' = C := by
      ext q; have := hπ q; simp [h0] at this; exact_mod_cast this
    exact this ▸ .refl
  | succ N ih =>
    obtain ⟨t, ht⟩ : ∃ t, π t ≠ 0 := by
      by_contra hc; push_neg at hc; simp [hc] at hN
    have hpre : t.pre ≤ C := by
      rw [Multiset.le_iff_count]
      intro q
      by_cases hq : q ∈ t.pre
      · have := hsat t ht q hq; have := count_pre_le_two t q; rw [hN] at *; omega
      · simp [Multiset.count_eq_zero.2 hq]
    have hf : t.Fires C (C - t.pre + t.post) := ⟨hpre, rfl⟩
    let π' : Transition Q → ℕ := Function.update π t (π t - 1)
    have hsplit : ∀ f : Transition Q → ℤ,
        ∑ s, (π s : ℤ) * f s = ∑ s, (π' s : ℤ) * f s + f t := by
      intro f
      rw [← add_sum_erase _ _ (mem_univ t), ← add_sum_erase _ _ (mem_univ t)]
      have : ∑ s ∈ univ.erase t, (π' s : ℤ) * f s = ∑ s ∈ univ.erase t, (π s : ℤ) * f s :=
        sum_congr rfl fun s hs => by simp [π', Function.update_of_ne (ne_of_mem_erase hs)]
      rw [this]
      simp only [π', Function.update_self]
      push_cast [Nat.one_le_iff_ne_zero.2 ht]
      ring
    have hN' : ∑ s, π' s = N := by
      have := hsplit (fun _ => 1)
      simp only [mul_one] at this
      exact_mod_cast (by rw [← Nat.cast_sum, ← Nat.cast_sum, hN] at this; omega :
        ((∑ s, π' s : ℕ) : ℤ) = N)
    refine Relation.ReflTransGen.head ⟨t, hT t ht, hf⟩ (ih (π := π') ?_ ?_ ?_ hN')
    · intro q
      rw [hπ q, hf.count_eq q, hsplit (fun s => s.delta q)]
      ring
    · intro s hs
      refine hT s ?_
      by_cases hst : s = t
      · exact hst ▸ ht
      · simpa [π', Function.update_of_ne hst] using hs
    · intro s hs q hq
      have hs' : π s ≠ 0 := by
        by_cases hst : s = t
        · exact hst ▸ ht
        · simpa [π', Function.update_of_ne hst] using hs
      have h1 := hsat s hs' q hq
      have h2 := count_pre_le_two t q
      have h3 := Multiset.count_le_of_le q hpre
      rw [hN] at h1
      simp only [Multiset.count_add, Multiset.count_sub]
      omega

namespace Protocol

variable {P : Protocol Q} {η : ℕ}

theorem IC_add_leaderless (hL : P.Leaderless) (i j : ℕ) : P.IC (i + j) = P.IC i + P.IC j := by
  simp [IC_leaderless hL, Multiset.replicate_add]

theorem IC_mul_leaderless (hL : P.Leaderless) (k i : ℕ) : P.IC (k * i) = k • P.IC i := by
  simp [IC_leaderless hL, Multiset.nsmul_replicate]

/-- **Lemma 5.2** (leaderless; with the hypothesis `b ≥ 1`, missing in the paper, see
`lemma_5_2_b_zero_false`; saturation is only required on pre-states of the support of `π`). -/
theorem lemma_5_2 (h : P.ComputesGe η) (hL : P.Leaderless) {a b : ℕ}
    {B Da Db D : Multiset Q} {S : Finset Q} {π : Transition Q → ℕ}
    (hB : IsBasisElem P.SC B S) (hDa : ∀ q ∈ Da, q ∈ S) (hDb : ∀ q ∈ Db, q ∈ S)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (h1 : P.Reach (P.IC a) D) (h1' : P.Reach D (B + Da))
    (h2 : FlowEq (P.IC b) Db π) (hT : ∀ t, π t ≠ 0 → t ∈ P.T)
    (hsat : ∀ t, π t ≠ 0 → ∀ q ∈ t.pre, 2 * ∑ t, π t ≤ D.count q) : η ≤ a := by
  -- `(∗)`: `D + λ IC(b) →* D + λ D_b`
  have hstep : P.Reach (D + P.IC b) (D + Db) :=
    lemma_5_1_ii (fun q => by rw [Multiset.count_add, Multiset.count_add]; push_cast; rw [h2 q]; ring)
      hT fun t ht q hq => (hsat t ht q hq).trans (by simp)
  have hstar : ∀ l : ℕ, P.Reach (D + l • P.IC b) (D + l • Db) := by
    intro l
    induction l with
    | zero => simpa using (Relation.ReflTransGen.refl : P.Reach D D)
    | succ l ih =>
      have e1 : D + (l + 1) • P.IC b = (D + P.IC b) + l • P.IC b := by rw [succ_nsmul]; abel
      have e2 : (D + Db) + l • P.IC b = (D + l • P.IC b) + Db := by abel
      have e3 : D + (l + 1) • Db = (D + l • Db) + Db := by rw [succ_nsmul]; abel
      rw [e1, e3]
      exact (MReach.add_right hstep _).trans (e2 ▸ MReach.add_right ih Db)
  refine h.le_of_pump hB hDa hDb ha hb fun l => ?_
  rw [IC_add_leaderless hL, IC_mul_leaderless hL]
  exact ((MReach.add_right h1 _).trans (hstar l)).trans (MReach.add_right h1' _)

/-- A state is *coverable* if some configuration reachable from some initial configuration
populates it. -/
def Coverable (P : Protocol Q) (q : Q) : Prop := ∃ i C, P.Reach (P.IC i) C ∧ q ∈ C

/-- **Lemma 5.3.** Let `C` be populated in `U = ⟦C⟧ ∋ x` and let some coverable state lie outside
`U`. Then some transition has its pre-states in `U` and some post-state outside `U`. -/
theorem lemma_5_3 (hL : P.Leaderless) {U : Finset Q} (hx : P.x ∈ U)
    (hcov : ∃ q, P.Coverable q ∧ q ∉ U) :
    ∃ t ∈ P.T, (∀ q ∈ t.pre, q ∈ U) ∧ ∃ q ∈ t.post, q ∉ U := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨q, ⟨i, C, hC, hqC⟩, hqU⟩ := hcov
  suffices ∀ C', P.Reach (P.IC i) C' → ∀ q ∈ C', q ∈ U from hqU (this C hC q hqC)
  intro C' hC'
  induction hC' with
  | refl =>
    intro q hq
    rw [IC_leaderless hL] at hq
    rw [Multiset.eq_of_mem_replicate hq]
    exact hx
  | tail _ hs ih =>
    obtain ⟨t, ht, hf⟩ := hs
    intro q hq
    rw [hf.2] at hq
    rcases Multiset.mem_add.1 hq with hq | hq
    · exact ih q (Multiset.mem_of_le (Multiset.sub_le_self _ _) hq)
    · exact hcon t ht (fun p hp => ih p (Multiset.mem_of_le hf.1 hp)) q hq

/-- **Lemma 5.4.** From `IC(3^n)` some configuration populating every coverable state is
reachable. -/
theorem lemma_5_4 (hL : P.Leaderless) :
    ∃ C, P.Reach (P.IC (3 ^ Fintype.card Q)) C ∧ ∀ q, P.Coverable q → q ∈ C := by
  classical
  have key : ∀ j, ∃ C, P.Reach (P.IC (3 ^ j)) C ∧ P.x ∈ C ∧
      ((∀ q, P.Coverable q → q ∈ C) ∨ j + 1 ≤ C.toFinset.card) := by
    intro j
    induction j with
    | zero => exact ⟨P.IC 1, .refl, by simp [IC_leaderless hL], .inr (by simp [IC_leaderless hL])⟩
    | succ j ih =>
      obtain ⟨C, hC, hxC, hor⟩ := ih
      have h3 : P.Reach (P.IC (3 ^ (j + 1))) (3 • C) := by
        rw [pow_succ, mul_comm, IC_mul_leaderless hL]
        exact MReach.nsmul hC 3
      by_cases hall : ∀ q, P.Coverable q → q ∈ C
      · exact ⟨3 • C, h3, Multiset.mem_nsmul.2 ⟨by omega, hxC⟩,
          .inl fun q hq => Multiset.mem_nsmul.2 ⟨by omega, hall q hq⟩⟩
      · have hcard := hor.resolve_left hall
        push_neg at hall
        obtain ⟨t, ht, hpre, q', hq'post, hq'U⟩ :=
          lemma_5_3 hL (U := C.toFinset) (by simpa using hxC)
            (by obtain ⟨q, h1, h2⟩ := hall; exact ⟨q, h1, by simpa using h2⟩)
        have hle : t.pre ≤ 2 • C := by
          rw [Multiset.le_iff_count]
          intro q
          by_cases hq : q ∈ t.pre
          · have : 0 < C.count q := Multiset.count_pos.2 (by simpa using hpre q hq)
            have := count_pre_le_two t q
            simp only [Multiset.count_nsmul]; omega
          · simp [Multiset.count_eq_zero.2 hq]
        have hf : t.Fires (2 • C) (2 • C - t.pre + t.post) := ⟨hle, rfl⟩
        refine ⟨C + (2 • C - t.pre + t.post), h3.trans ?_, Multiset.mem_add.2 (.inl hxC),
          .inr ?_⟩
        · rw [show 3 • C = C + 2 • C by rw [show (3 : ℕ) = 1 + 2 from rfl, add_nsmul, one_nsmul]]
          exact MReach.add_left (.single ⟨t, ht, hf⟩) C
        · have hsub : insert q' C.toFinset ⊆ (C + (2 • C - t.pre + t.post)).toFinset := by
            intro q hq
            rcases mem_insert.1 hq with rfl | hq
            · simp [hq'post]
            · simp only [Multiset.mem_toFinset] at hq ⊢; exact Multiset.mem_add.2 (.inl hq)
          have := card_le_card hsub
          rw [card_insert_of_notMem hq'U] at this
          omega
  obtain ⟨C, hC, -, hor⟩ := key (Fintype.card Q)
  refine ⟨C, hC, hor.resolve_right fun h => ?_⟩
  have := card_le_univ C.toFinset
  omega

/-- Our Pottier-type constant `ξ(n) = 4^(2^n - 1)` (Definition 6 uses `2(2|T|+1)^|Q|`). -/
def xi (n : ℕ) : ℕ := 4 ^ (2 ^ n - 1)

theorem one_le_xi (n : ℕ) : 1 ≤ xi n := Nat.one_le_pow _ _ (by norm_num)

theorem count_IC (hL : P.Leaderless) (i : ℕ) (q : Q) :
    (P.IC i).count q = if q = P.x then i else 0 := by
  rw [IC_leaderless hL, Multiset.count_replicate]
  split_ifs <;> simp_all

/-- Lemma 5.8, main case: `x ∉ S` and `C(x) = 0`. -/
theorem lemma_5_8_core (hL : P.Leaderless) {i : ℕ} {C : Multiset Q} {π : Transition Q → ℕ}
    (hπ : FlowEq (P.IC i) C π) {S : Finset Q}
    (hconc : xi (Fintype.card Q) * ∑ q ∈ Sᶜ, C.count q < i) :
    ∃ j θ C', 0 < j ∧ j ≤ xi (Fintype.card Q) ∧ ∑ t, θ t ≤ xi (Fintype.card Q) ∧
      (∀ t, θ t ≤ π t) ∧ FlowEq (P.IC j) C' θ ∧ ∀ q ∈ C', q ∈ S := by
  classical
  set K := xi (Fintype.card Q)
  let A : Q → Transition Q ⊕ Unit → ℤ := fun q v =>
    Sum.elim (fun t => t.delta q) (fun _ => if q = P.x then 1 else 0) v
  have hA : ∀ q v, |A q v| ≤ 2 := by
    intro q v
    cases v with
    | inl t => exact Transition.abs_delta_le t q
    | inr _ => simp only [A, Sum.elim_inr]; split_ifs <;> simp
  let X : Transition Q ⊕ Unit → ℕ := Sum.elim π (fun _ => i)
  let row : Q → (Transition Q ⊕ Unit → ℕ) → ℤ := fun q y => ∑ v, A q v * (y v : ℤ)
  have hrow : ∀ q y, row q y =
      (if q = P.x then (y (Sum.inr ()) : ℤ) else 0) + ∑ t, (y (Sum.inl t) : ℤ) * t.delta q := by
    intro q y
    simp only [row, A, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.univ_unit,
      sum_singleton]
    split_ifs <;> simp [mul_comm, add_comm]
  have hrowX : ∀ q, row q X = C.count q := by
    intro q
    rw [hrow, hπ q, count_IC hL]
    simp only [X, Sum.elim_inl, Sum.elim_inr]
    split_ifs <;> simp
  obtain ⟨s, hs, hsy⟩ := Cslib.exists_small_decomposition 2 (by norm_num) A hA X
    (fun q => by rw [show (∑ j, A q j * (X j : ℤ)) = row q X from rfl, hrowX]; positivity)
  -- linear forms on pieces
  let jv : (Transition Q ⊕ Unit → ℕ) → ℤ := fun y => y (Sum.inr ())
  let m : (Transition Q ⊕ Unit → ℕ) → ℤ := fun y => ∑ q ∈ Sᶜ, row q y
  have hjsum : (s.map jv).sum = i := by
    have := Cslib.DiophantineDecomposition.sum_map_linear
      (fun v => Sum.elim (fun _ => (0 : ℤ)) (fun _ => 1) v) s
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, zero_mul, sum_const_zero,
      zero_add, one_mul, Fintype.univ_unit, sum_singleton, hs] at this
    exact this
  have hmsum : (s.map m).sum = ∑ q ∈ Sᶜ, (C.count q : ℤ) := by
    have := Cslib.DiophantineDecomposition.sum_map_linear (fun v => ∑ q ∈ Sᶜ, A q v) s
    have e : ∀ y : Transition Q ⊕ Unit → ℕ, ∑ v, (∑ q ∈ Sᶜ, A q v) * (y v : ℤ) = m y := by
      intro y; simp only [m, row, sum_mul]; exact sum_comm
    simp only [e, hs] at this
    rw [this]
    exact sum_congr rfl fun q _ => hrowX q
  have hrow_nonneg : ∀ y ∈ s, ∀ q, 0 ≤ row q y := fun y hy q => (hsy y hy).1 q
  have hjK : ∀ y ∈ s, jv y ≤ K := by
    intro y hy
    have h := (hsy y hy).2
    rw [Fintype.sum_sum_type] at h
    simp only [Fintype.univ_unit, sum_singleton] at h
    simp only [jv]
    show ((y (Sum.inr ()) : ℕ) : ℤ) ≤ ((4 ^ (2 ^ Fintype.card Q - 1) : ℕ) : ℤ)
    exact_mod_cast (by norm_num at h; omega : y (Sum.inr ()) ≤ 4 ^ (2 ^ Fintype.card Q - 1))
  -- the counting argument
  have hex : ∃ y ∈ s, 0 < jv y ∧ m y ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have hle : ∀ y ∈ s, jv y ≤ K * m y := by
      intro y hy
      have hm0 : 0 ≤ m y := sum_nonneg fun q _ => hrow_nonneg y hy q
      by_cases hj : 0 < jv y
      · have := hcon y hy hj
        nlinarith [hjK y hy]
      · push_neg at hj
        have : (0 : ℤ) ≤ K := by positivity
        nlinarith
    have := Multiset.sum_map_le_sum_map _ _ hle
    rw [hjsum, Multiset.sum_map_mul_left, hmsum] at this
    have h2 : ((K * ∑ q ∈ Sᶜ, C.count q : ℕ) : ℤ) < i := by exact_mod_cast hconc
    push_cast at h2
    linarith
  obtain ⟨y, hy, hjpos, hm⟩ := hex
  have hrowS : ∀ q ∈ Sᶜ, row q y = 0 := by
    have := (sum_eq_zero_iff_of_nonneg fun q _ => hrow_nonneg y hy q).1
      (le_antisymm hm (sum_nonneg fun q _ => hrow_nonneg y hy q))
    exact this
  refine ⟨y (Sum.inr ()), fun t => y (Sum.inl t), ofCount fun q => (row q y).toNat,
    by have := hjpos; simp only [jv] at this; exact_mod_cast this,
    by have := hjK y hy; simp only [jv] at this; exact_mod_cast this, ?_, ?_, ?_, ?_⟩
  · have h := (hsy y hy).2
    rw [Fintype.sum_sum_type] at h
    exact (Nat.le_add_right _ _).trans h
  · intro t
    have := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem (fun y => y (Sum.inl t)) hy)
    rw [← Pi.multiset_sum_apply, hs] at this
    exact this
  · intro q
    rw [count_ofCount, Int.toNat_of_nonneg (hrow_nonneg y hy q), hrow, count_IC hL]
    split_ifs <;> simp
  · intro q hq
    by_contra hqS
    rw [← Multiset.count_pos, count_ofCount, hrowS q (by simpa using hqS)] at hq
    simp at hq

/-- **Lemma 5.8** (with Corollary 5.7 replaced by `Cslib.exists_small_decomposition`). If
`IC(i) =π⇒ C` and `ξ · C(Q \ S) < i`, then `IC(j) =θ⇒ C'` for some `0 < j ≤ ξ`, some `θ ≤ π` with
`|θ| ≤ ξ`, and some `C' ∈ ℕ^S`. (The paper's hypothesis "`C` is `1/ξ`-concentrated", i.e.
`ξ · C(Q \ S) ≤ i`, is not sufficient for its proof; the strict version holds in Theorem 5.9.) -/
theorem lemma_5_8 (hL : P.Leaderless) {i : ℕ} {C : Multiset Q} {π : Transition Q → ℕ}
    (hπ : FlowEq (P.IC i) C π) {S : Finset Q}
    (hconc : xi (Fintype.card Q) * ∑ q ∈ Sᶜ, C.count q < i) :
    ∃ j θ C', 0 < j ∧ j ≤ xi (Fintype.card Q) ∧ ∑ t, θ t ≤ xi (Fintype.card Q) ∧
      (∀ t, θ t ≤ π t) ∧ FlowEq (P.IC j) C' θ ∧ ∀ q ∈ C', q ∈ S := by
  classical
  set K := xi (Fintype.card Q)
  by_cases hxS : P.x ∈ S
  · refine ⟨1, 0, {P.x}, one_pos, one_le_xi _, by simp, fun _ => Nat.zero_le _, fun q => ?_,
      fun q hq => by rw [Multiset.mem_singleton.1 hq]; exact hxS⟩
    simp [IC_leaderless hL]
  -- remove the agents in `x`
  set l := C.count P.x
  have hli : l ≤ i := by
    have := Multiset.count_le_card P.x C
    rw [hπ.card_eq, card_IC, show P.L = 0 from hL] at this
    simpa using this
  have hπ' : FlowEq (P.IC (i - l)) (C - Multiset.replicate l P.x) π := by
    intro q
    have h := hπ q
    rw [count_IC hL] at h
    rw [count_IC hL, Multiset.count_sub, Multiset.count_replicate]
    by_cases hq : q = P.x
    · subst hq; simp only [ite_true] at h ⊢; push_cast [hli]; simp [l] at h ⊢; linarith
    · simp only [hq, ite_false, Ne.symm hq] at h ⊢; simpa using h
  have hxSc : P.x ∈ Sᶜ := by simpa using hxS
  have hsum : ∑ q ∈ Sᶜ, (C - Multiset.replicate l P.x).count q + l = ∑ q ∈ Sᶜ, C.count q := by
    rw [← add_sum_erase _ _ hxSc, ← add_sum_erase _ _ hxSc]
    have : ∑ q ∈ Sᶜ.erase P.x, (C - Multiset.replicate l P.x).count q =
        ∑ q ∈ Sᶜ.erase P.x, C.count q :=
      sum_congr rfl fun q hq => by
        simp [Multiset.count_sub, Multiset.count_replicate, Ne.symm (ne_of_mem_erase hq)]
    rw [this]
    simp [Multiset.count_sub, Multiset.count_replicate, l]
    omega
  refine lemma_5_8_core hL hπ' ?_
  have hK := one_le_xi (Fintype.card Q)
  set σ := ∑ q ∈ Sᶜ, (C - Multiset.replicate l P.x).count q
  have h1 : K * σ + K * l < i := by rw [← mul_add]; exact hsum ▸ hconc
  have h2 : l ≤ K * l := Nat.le_mul_of_pos_left l hK
  show K * σ < i - l
  omega

/-- Every transition fired along a firing sequence from a configuration reachable from an initial
configuration has coverable pre-states. -/
theorem firesSeq_pre_coverable {i : ℕ} {w : List (Transition Q)} {C C' : Multiset Q}
    (hC : P.Reach (P.IC i) C) (hw : FiresSeq w C C') (hwT : ∀ t ∈ w, t ∈ P.T) :
    ∀ t ∈ w, ∀ q ∈ t.pre, P.Coverable q := by
  induction w generalizing C with
  | nil => simp
  | cons t w ih =>
    obtain ⟨C₁, ht, hw'⟩ := hw
    intro s hs q hq
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ⟨i, C, hC, Multiset.mem_of_le ht.1 hq⟩
    · exact ih (hC.tail ⟨t, hwT t (by simp), ht⟩) hw' (fun u hu => hwT u (by simp [hu])) s hs q hq

theorem two_le_beta (n : ℕ) : 2 ≤ beta n := by
  unfold beta; exact Nat.le_self_pow (by omega) 2

/-- **Theorem 5.9** (first inequality, with our constant `ξ(n) = 4^(2^n - 1)`): a leaderless
protocol with `n` states computing `x ≥ η` satisfies `η ≤ ξ n β 3^n`. -/
theorem theorem_5_9_le (h : P.ComputesGe η) (hL : P.Leaderless) :
    η ≤ xi (Fintype.card Q) * Fintype.card Q * beta (Fintype.card Q) * 3 ^ Fintype.card Q := by
  classical
  have hn : 1 ≤ Fintype.card Q := Fintype.card_pos_iff.2 ⟨P.x⟩
  have hK := one_le_xi (Fintype.card Q)
  have hβ := two_le_beta (Fintype.card Q)
  have h3 : 3 ≤ 3 ^ Fintype.card Q := Nat.le_self_pow (by omega) 3
  obtain ⟨c, hc⟩ : ∃ c, c = xi (Fintype.card Q) * Fintype.card Q * beta (Fintype.card Q) :=
    ⟨_, rfl⟩
  rw [← hc]
  have hnβ : 2 ≤ Fintype.card Q * beta (Fintype.card Q) := by nlinarith
  have hc2 : 2 * xi (Fintype.card Q) ≤ c := by rw [hc, mul_assoc]; nlinarith
  have ha : 2 ≤ c * 3 ^ Fintype.card Q := by nlinarith
  obtain ⟨Csat, hCsat, hcov⟩ := lemma_5_4 hL
  have hD : P.Reach (P.IC (c * 3 ^ Fintype.card Q)) (c • Csat) := by
    rw [IC_mul_leaderless hL]; exact MReach.nsmul hCsat c
  obtain ⟨C, hDC, hSC⟩ := h.exists_SC ha hD
  obtain ⟨Bs, -, hBs, hBcov⟩ := exists_small_basis_SC (P := P)
  obtain ⟨p, hp, Da, hDa, rfl⟩ := (hBcov C).1 hSC
  obtain ⟨hBnorm, hBe⟩ := hBs p hp
  obtain ⟨w, hwT, hw⟩ := MReach.exists_firesSeq (hD.trans hDC)
  have hflow := hw.flowEq
  -- concentration: `ξ · (B + D_a)(Q \ S) ≤ ξ n β < a`
  have hconc : xi (Fintype.card Q) * ∑ q ∈ p.2ᶜ, (p.1 + Da).count q <
      c * 3 ^ Fintype.card Q := by
    have e : ∑ q ∈ p.2ᶜ, (p.1 + Da).count q = ∑ q ∈ p.2ᶜ, p.1.count q :=
      sum_congr rfl fun q hq => by
        rw [Multiset.count_add, Multiset.count_eq_zero.2 fun h' => (mem_compl.1 hq) (hDa q h'),
          add_zero]
    have hle : ∑ q ∈ p.2ᶜ, p.1.count q ≤ Fintype.card Q * beta (Fintype.card Q) :=
      (sum_le_sum_of_subset (subset_univ _)).trans
        ((sum_le_sum fun q _ => hBnorm q).trans (by simp))
    rw [e]
    have h1 : xi (Fintype.card Q) * ∑ q ∈ p.2ᶜ, p.1.count q ≤ c := by
      rw [hc, mul_assoc]; exact Nat.mul_le_mul_left _ hle
    have h2 : 1 ≤ c := by omega
    nlinarith
  obtain ⟨j, θ, C', hj0, -, hθK, hθπ, hθflow, hC'S⟩ := lemma_5_8 hL hflow hconc
  have hmem : ∀ t, θ t ≠ 0 → t ∈ w := fun t ht =>
    List.count_pos_iff.1 (Nat.pos_of_ne_zero fun h0 => ht (Nat.eq_zero_of_le_zero
      (h0 ▸ hθπ t)))
  refine lemma_5_2 h hL hBe hDa hC'S ha hj0 hD hDC hθflow (fun t ht => hwT t (hmem t ht)) ?_
  intro t ht q hq
  have hcq : P.Coverable q :=
    firesSeq_pre_coverable (i := c * 3 ^ Fintype.card Q) .refl hw hwT t (hmem t ht) q hq
  have : 1 ≤ Csat.count q := Multiset.count_pos.2 (hcov q hcq)
  rw [Multiset.count_nsmul]
  calc 2 * ∑ t, θ t ≤ 2 * xi (Fintype.card Q) := by omega
    _ ≤ c := hc2
    _ ≤ c * Csat.count q := Nat.le_mul_of_pos_right c this

end Protocol

theorem two_pow_le_factorial_succ (m : ℕ) : 2 ^ m ≤ (m + 1).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.factorial_succ]
    nlinarith

/-- The arithmetic of Theorem 5.9: `ξ n β 3^n ≤ 2^((2n+2)!)`. -/
theorem xi_mul_le (n : ℕ) : Protocol.xi n * n * beta n * 3 ^ n ≤ 2 ^ (2 * n + 2).factorial := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set F := (2 * n + 1).factorial
  have hxi : Protocol.xi n ≤ 2 ^ (2 ^ (n + 1)) := by
    unfold Protocol.xi
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
    exact Nat.pow_le_pow_right (by omega) (by rw [pow_succ]; omega)
  have hnn : n ≤ 2 ^ n := (Nat.lt_two_pow_self).le
  have h3 : 3 ^ n ≤ 2 ^ (2 * n) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) n
  have hF1 : 2 ^ (n + 1) ≤ F :=
    (two_pow_le_factorial_succ (n + 1)).trans (Nat.factorial_le (by omega))
  have hF2 : 3 * n + 1 ≤ F := by
    have h1 : F = (2 * n + 1) * (2 * n).factorial := Nat.factorial_succ _
    have h2 : 2 * n ≤ (2 * n).factorial := Nat.self_le_factorial _
    rw [h1]; nlinarith
  have hfac : (2 * n + 2).factorial = (2 * n + 2) * F := Nat.factorial_succ _
  calc Protocol.xi n * n * beta n * 3 ^ n
      ≤ 2 ^ (2 ^ (n + 1)) * 2 ^ n * 2 ^ (2 * F + 1) * 2 ^ (2 * n) := by
        gcongr; exact le_of_eq rfl
    _ = 2 ^ (2 ^ (n + 1) + n + (2 * F + 1) + 2 * n) := by simp only [pow_add]
    _ ≤ 2 ^ (2 * n + 2).factorial := by
        apply Nat.pow_le_pow_right (by omega)
        rw [hfac]; nlinarith

namespace Protocol

variable {P : Protocol Q} {η : ℕ}

/-- **Theorem 5.9.** A leaderless population protocol with `n` states computing `x ≥ η` satisfies
`η ≤ 2^((2n+2)!)`; hence `BB(n) ≤ 2^((2n+2)!)` and `STATE(η) ∈ Ω(log log η)`. -/
theorem theorem_5_9 (h : P.ComputesGe η) (hL : P.Leaderless) :
    η ≤ 2 ^ (2 * Fintype.card Q + 2).factorial :=
  (theorem_5_9_le h hL).trans (xi_mul_le _)

end Protocol

end Podc.PPStateComplexity
