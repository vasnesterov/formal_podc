import Papers.PODC2019.AutomaticSpeedup.SuperweakDefs

/-!
# Lemma 1 of Brandt (PODC 2019, §5.1): the dominant set `P∞`

Auxiliary material for `lemma_1` (see `Lemmas123.lean`):
* `TGood k m`: the node condition of `tritHalf k` without the cardinality constraint;
* `CapEq k a b`: `a` and `b` have the same multiplicities, capped at `k + 1`; `TGood` is invariant
  under `CapEq` (`CapEq.good`), which is the core of the paper's exchange argument;
* `lemma_1_card`: Lemma 1 for configurations of cardinality exactly `Δ` (as in the paper).
-/

namespace AutomaticSpeedup

open Problem

variable {k : ℕ}

/-- The node condition of `tritHalf k` (without the cardinality constraint). -/
def TGood (k : ℕ) (m : Multiset (Trit k)) : Prop :=
  ∃ j, countAt m j 0 ≤ k ∧ countAt m j 0 < countAt m j 2

theorem countAt_eq_sum (m : Multiset (Trit k)) (j : Fin k) (x : Fin 3) :
    countAt m j x = ∑ t ∈ Finset.univ.filter (fun t : Trit k => t j = x), m.count t := by
  rw [Finset.sum_filter]
  unfold countAt
  rw [← Multiset.sum_count_eq_card (s := Finset.univ) (fun a _ => Finset.mem_univ a)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Multiset.count_filter]

theorem countAt_cons (x : Trit k) (m : Multiset (Trit k)) (j : Fin k) (y : Fin 3) :
    countAt (x ::ₘ m) j y = countAt m j y + if x j = y then 1 else 0 := by
  unfold countAt
  rw [Multiset.filter_cons]
  split_ifs <;> simp [add_comm]

theorem countAt_add (a b : Multiset (Trit k)) (j : Fin k) (y : Fin 3) :
    countAt (a + b) j y = countAt a j y + countAt b j y := by
  simp [countAt, Multiset.filter_add]

theorem count_le_countAt (m : Multiset (Trit k)) (p : Trit k) (j : Fin k) :
    m.count p ≤ countAt m j (p j) := by
  unfold countAt
  calc m.count p = (m.filter fun a => a j = p j).count p := by
          rw [Multiset.count_filter]; simp
    _ ≤ _ := Multiset.count_le_card _ _

theorem min_sum_eq {ι : Type*} (s : Finset ι) (f g : ι → ℕ) (K : ℕ)
    (h : ∀ i, min (f i) K = min (g i) K) : min (∑ i ∈ s, f i) K = min (∑ i ∈ s, g i) K := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have := h a
    omega

/-- Equal multiplicities, capped at `k + 1`. -/
def CapEq (k : ℕ) (a b : Multiset (Trit k)) : Prop :=
  ∀ t, min (a.count t) (k + 1) = min (b.count t) (k + 1)

theorem CapEq.countAt {a b : Multiset (Trit k)} (h : CapEq k a b) (j : Fin k) (x : Fin 3) :
    min (countAt a j x) (k + 1) = min (countAt b j x) (k + 1) := by
  rw [countAt_eq_sum, countAt_eq_sum]; exact min_sum_eq _ _ _ _ h

theorem CapEq.good {a b : Multiset (Trit k)} (h : CapEq k a b) : TGood k a → TGood k b := by
  rintro ⟨j, h1, h2⟩
  have e0 := h.countAt j 0
  have e2 := h.countAt j 2
  exact ⟨j, by omega, by omega⟩

/-- Exchanging one copy of a frequent element for another frequent element. -/
theorem capEq_of_cons {a b : Multiset (Trit k)} {p y : Trit k} (h : p ::ₘ a = y ::ₘ b)
    (hp : k + 1 ≤ a.count p) (hy : k + 1 ≤ b.count y) : CapEq k a b := by
  intro t
  have := congrArg (Multiset.count t) h
  simp only [Multiset.count_cons] at this
  split_ifs at this with h1 h2 h2 <;> subst_vars <;> omega

/-- Pigeonhole: a multiset of more than `n · 3^k` trit sequences has an element of multiplicity
at least `n + 1`. -/
theorem exists_count_gt (m : Multiset (Trit k)) (n : ℕ) (h : n * 3 ^ k < Multiset.card m) :
    ∃ p, n + 1 ≤ m.count p := by
  by_contra hc
  push Not at hc
  have e := Multiset.sum_count_eq_card (s := Finset.univ) (m := m) (fun a _ => Finset.mem_univ a)
  have : ∑ p ∈ (Finset.univ : Finset (Trit k)), m.count p ≤ ∑ _p ∈ (Finset.univ : Finset (Trit k)), n :=
    Finset.sum_le_sum fun p _ => by have := hc p; omega
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    smul_eq_mul] at this
  rw [e] at this
  rw [mul_comm] at h
  omega

/-! ### Choices -/

theorem good_of_nodeAll {Δ : ℕ} {m : Multiset (Set (Trit k))} (h : (tritHalf k).NodeAll Δ m)
    {q : Multiset (Trit k)} (hq : Multiset.Rel (· ∈ ·) q m) : TGood k q :=
  (h.2.2 q hq).2

theorem exists_bad_of_not_nodeAll {Δ : ℕ} {m : Multiset (Set (Trit k))}
    (hm : Multiset.card m = Δ) (h : ¬ (tritHalf k).NodeAll Δ m) :
    ∃ q, Multiset.Rel (· ∈ ·) q m ∧ ¬ TGood k q := by
  unfold NodeAll at h
  push Not at h
  obtain ⟨q, hq, hq'⟩ := h hm.le (fun _ _ => Set.subset_univ _)
  exact ⟨q, hq, fun hg => hq' ⟨(Multiset.card_eq_card_of_rel hq).trans hm, hg⟩⟩

theorem rel_replicate_right' {α β : Type*} {r : α → β → Prop} {m : Multiset α} {b : β} {n : ℕ} :
    Multiset.Rel r m (Multiset.replicate n b) ↔ Multiset.card m = n ∧ ∀ x ∈ m, r x b := by
  induction n generalizing m with
  | zero => simp [Multiset.rel_zero_right]; rintro rfl; simp
  | succ n ih =>
    rw [Multiset.replicate_succ, Multiset.rel_cons_right]
    constructor
    · rintro ⟨a, m', ha, hm', rfl⟩
      obtain ⟨h1, h2⟩ := ih.1 hm'
      refine ⟨by simp [h1], fun x hx => ?_⟩
      rcases Multiset.mem_cons.1 hx with rfl | hx
      exacts [ha, h2 x hx]
    · rintro ⟨h1, h2⟩
      obtain ⟨a, m', rfl⟩ : ∃ a m', m = a ::ₘ m' := by
        obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 (by omega : 0 < Multiset.card m)
        exact ⟨a, Multiset.exists_cons_of_mem ha⟩
      refine ⟨a, m', h2 a (Multiset.mem_cons_self _ _), ih.2 ⟨by simpa using h1,
        fun x hx => h2 x (Multiset.mem_cons_of_mem hx)⟩, rfl⟩

theorem rel_mem_replicate_add {α : Type*} {q : Multiset α} {n : ℕ} {A : Set α}
    {R : Multiset (Set α)} :
    Multiset.Rel (· ∈ ·) q (Multiset.replicate n A + R) ↔
      ∃ a r, Multiset.card a = n ∧ (∀ x ∈ a, x ∈ A) ∧ Multiset.Rel (· ∈ ·) r R ∧ q = a + r := by
  rw [Multiset.rel_add_right]
  simp only [rel_replicate_right']
  constructor
  · rintro ⟨a, r, ⟨h1, h2⟩, h3, rfl⟩; exact ⟨a, r, h1, h2, h3, rfl⟩
  · rintro ⟨a, r, h1, h2, h3, rfl⟩; exact ⟨a, r, ⟨h1, h2⟩, h3, rfl⟩

theorem decomp_count {α : Type*} [DecidableEq α] (Q : Multiset α) (A : α) :
    Q = Multiset.replicate (Q.count A) A + Q.filter (· ≠ A) := by
  rw [← Multiset.filter_eq' Q A]
  exact (Multiset.filter_add_not _ Q).symm

theorem erase_decomp {α : Type*} [DecidableEq α] (Q : Multiset α) (A : α) :
    Q.erase A = Multiset.replicate (Q.count A - 1) A + Q.filter (· ≠ A) := by
  by_cases hA : A ∈ Q
  · obtain ⟨c, hc⟩ : ∃ c, Q.count A = c + 1 :=
      ⟨Q.count A - 1, by have := Multiset.count_pos.2 hA; omega⟩
    conv_lhs => rw [decomp_count Q A, hc, Multiset.replicate_succ, Multiset.cons_add,
      Multiset.erase_cons_head]
    rw [hc]; rfl
  · rw [Multiset.erase_of_notMem hA, Multiset.count_eq_zero_of_notMem hA]
    simpa using (Multiset.filter_eq_self.2 fun a ha (h : a = A) => hA (h ▸ ha)).symm

/-! ### Arithmetic -/

theorem three_mul_add_pow_le (hk : 2 ≤ k) : 3 * k + 3 ^ k ≤ 4 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ, pow_succ]; omega

theorem freqBound_le (hk : 2 ≤ k) : (k + 1) * 3 ^ k * 2 ^ (3 ^ k) ≤ 2 ^ (4 ^ k) := by
  have h1 : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have h2 : 3 ^ k ≤ 2 ^ (2 * k) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) k
  calc (k + 1) * 3 ^ k * 2 ^ (3 ^ k) ≤ 2 ^ k * 2 ^ (2 * k) * 2 ^ (3 ^ k) := by gcongr
    _ = 2 ^ (3 * k + 3 ^ k) := by rw [← pow_add, ← pow_add]; ring_nf
    _ ≤ 2 ^ (4 ^ k) := Nat.pow_le_pow_right (by norm_num) (three_mul_add_pow_le hk)

/-! ### Lemma 1 -/

section
variable {Δ : ℕ} {Q : Multiset (Set (Trit k))}

theorem card_cons_erase_eq {α : Type*} [DecidableEq α] {Q : Multiset α} {A : α} (B : α)
    (hA : A ∈ Q) : Multiset.card (B ::ₘ Q.erase A) = Multiset.card Q := by
  rw [Multiset.card_cons, Multiset.card_erase_of_mem hA]
  have := Multiset.card_pos_iff_exists_mem.2 ⟨A, hA⟩
  rw [Nat.pred_eq_sub_one]; omega

/-- Two distinct elements of a configuration in `h_1(Δ)` cannot both have multiplicity
`> (k+1)·3^k`: if `B ⊄ A`, enlarging one copy of `A` to `A ∪ B` would keep Property A. -/
theorem freq_core (hQ : Q ∈ (tritOne k).h Δ) (hc : Multiset.card Q = Δ)
    {A B : Set (Trit k)} (hAB : ¬ B ⊆ A) (hA : (k + 1) * 3 ^ k < Q.count A)
    (hB : (k + 1) * 3 ^ k ≤ Q.count B) : False := by
  have hne : A ≠ B := fun h => hAB (h ▸ subset_rfl)
  have hAQ : A ∈ Q := Multiset.count_pos.1 (by omega)
  have hss : A ⊂ A ∪ B := Set.ssubset_iff_subset_ne.2
    ⟨Set.subset_union_left, fun h => hAB (by rw [h]; exact Set.subset_union_right)⟩
  have hmax := hQ.2 A hAQ (A ∪ B) hss
  obtain ⟨q'', hq'', hbad⟩ :=
    exists_bad_of_not_nodeAll ((card_cons_erase_eq _ hAQ).trans hc) hmax
  obtain ⟨x, q0, hx, hq0, rfl⟩ := Multiset.rel_cons_right.1 hq''
  have hq0' := hq0
  set R := (Q.filter (· ≠ A)).filter (· ≠ B)
  have hF : Q.filter (· ≠ A) = Multiset.replicate (Q.count B) B + R := by
    conv_lhs => rw [decomp_count (Q.filter (· ≠ A)) B]
    rw [show (Q.filter (· ≠ A)).count B = Q.count B by rw [Multiset.count_filter]; simp [hne.symm]]
  have hE : Q.erase A =
      Multiset.replicate (Q.count A - 1) A + (Multiset.replicate (Q.count B) B + R) := by
    rw [erase_decomp, hF]
  have hQd : Q = Multiset.replicate (Q.count A) A + (Multiset.replicate (Q.count B) B + R) := by
    conv_lhs => rw [decomp_count Q A]
    rw [hF]
  rw [hE] at hq0
  obtain ⟨a, q1, ha1, ha2, hq1, rfl⟩ := rel_mem_replicate_add.1 hq0
  obtain ⟨b, r, hb1, hb2, hr, rfl⟩ := rel_mem_replicate_add.1 hq1
  rcases hx with hxA | hxB
  · apply hbad
    refine good_of_nodeAll hQ.1 ?_
    rw [← Multiset.cons_erase hAQ]
    exact Multiset.Rel.cons hxA hq0'
  · have hM : (k + 1) * 3 ^ k = k * 3 ^ k + 3 ^ k := by ring
    have h3 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    obtain ⟨p, hp⟩ := exists_count_gt a k (by rw [ha1]; omega)
    obtain ⟨y, hy⟩ := exists_count_gt (x ::ₘ b) (k + 1) (by rw [Multiset.card_cons, hb1]; omega)
    have hpa : p ∈ a := Multiset.count_pos.1 (by omega)
    have hyb : y ∈ x ::ₘ b := Multiset.count_pos.1 (by omega)
    apply hbad
    have hq : TGood k ((p ::ₘ a) + ((x ::ₘ b).erase y + r)) := by
      refine good_of_nodeAll hQ.1 ?_
      rw [hQd]
      refine rel_mem_replicate_add.2 ⟨p ::ₘ a, _, by rw [Multiset.card_cons, ha1]; omega, ?_,
        rel_mem_replicate_add.2 ⟨(x ::ₘ b).erase y, r, ?_, ?_, hr, rfl⟩, rfl⟩
      · intro z hz
        rcases Multiset.mem_cons.1 hz with rfl | hz
        exacts [ha2 _ hpa, ha2 z hz]
      · rw [Multiset.card_erase_of_mem hyb, Multiset.card_cons, hb1]; simp
      · intro z hz
        rcases Multiset.mem_cons.1 (Multiset.mem_of_mem_erase hz) with rfl | hz
        exacts [hxB, hb2 z hz]
    refine CapEq.good (capEq_of_cons (p := y) (y := p) ?_ ?_ ?_) hq
    · have he : x ::ₘ b = y ::ₘ (x ::ₘ b).erase y := (Multiset.cons_erase hyb).symm
      set e := (x ::ₘ b).erase y
      simp only [← Multiset.singleton_add] at he ⊢
      calc {y} + ({p} + a + (e + r)) = {p} + a + ({y} + e) + r := by abel
        _ = {p} + a + ({x} + b) + r := by rw [he]
        _ = {p} + ({x} + (a + (b + r))) := by abel
    · simp only [Multiset.count_add, Multiset.count_erase_self]
      omega
    · simp only [Multiset.count_cons, Multiset.count_add]
      split_ifs <;> omega

theorem freq_unique (hQ : Q ∈ (tritOne k).h Δ) (hc : Multiset.card Q = Δ)
    {A B : Set (Trit k)} (hA : (k + 1) * 3 ^ k < Q.count A)
    (hB : (k + 1) * 3 ^ k < Q.count B) : A = B := by
  by_contra hne
  by_cases hBA : B ⊆ A
  · exact freq_core hQ hc (A := B) (B := A) (fun h => hne (Set.Subset.antisymm h hBA)) hB hA.le
  · exact freq_core hQ hc hBA hA hB.le

/-- A frequent element of a configuration in `h_1(Δ)` contains `11…1`. -/
theorem ones_mem_of_count (hQ : Q ∈ (tritOne k).h Δ) (hc : Multiset.card Q = Δ)
    {P : Set (Trit k)} (hP : k * 3 ^ k + 1 < Q.count P) : ones k ∈ P := by
  by_contra hno
  have hPQ : P ∈ Q := Multiset.count_pos.1 (by omega)
  have hmax := hQ.2 P hPQ _ (Set.ssubset_insert hno)
  obtain ⟨q'', hq'', hbad⟩ :=
    exists_bad_of_not_nodeAll ((card_cons_erase_eq _ hPQ).trans hc) hmax
  obtain ⟨x, q0, hx, hq0, rfl⟩ := Multiset.rel_cons_right.1 hq''
  have hq0' := hq0
  rw [erase_decomp] at hq0
  obtain ⟨a, r, ha1, ha2, hr, rfl⟩ := rel_mem_replicate_add.1 hq0
  rcases Set.mem_insert_iff.1 hx with rfl | hxP
  · obtain ⟨p, hp⟩ := exists_count_gt a k (by rw [ha1]; omega)
    have hpa : p ∈ a := Multiset.count_pos.1 (by omega)
    have hgood : TGood k (p ::ₘ (a + r)) := good_of_nodeAll hQ.1 (by
      rw [← Multiset.cons_erase hPQ]; exact Multiset.Rel.cons (ha2 p hpa) hq0')
    apply hbad
    obtain ⟨j, h1, h2⟩ := hgood
    have hc2 : a.count p ≤ countAt (a + r) j (p j) :=
      le_trans (by simp [Multiset.count_add]) (count_le_countAt _ _ _)
    have o0 : ¬ (ones k j = 0) := by simp [ones]
    have o2 : ¬ (ones k j = 2) := by simp [ones]
    simp only [countAt_cons] at h1 h2
    refine ⟨j, ?_, ?_⟩ <;> simp only [countAt_cons, o0, o2, ↓reduceIte, add_zero]
    · split_ifs at h1 <;> omega
    · by_cases hp2 : p j = 2
      · rw [hp2] at hc2
        split_ifs at h1 h2 <;> omega
      · simp only [hp2, ↓reduceIte, add_zero] at h2
        split_ifs at h1 h2 <;> omega
  · apply hbad
    exact good_of_nodeAll hQ.1 (by
      rw [← Multiset.cons_erase hPQ]; exact Multiset.Rel.cons hxP hq0')

/-- **Lemma 1** for configurations with exactly `Δ` elements (as in the paper, where
`h_1(Δ)` consists of multisets `{W_1, …, W_Δ}`). -/
theorem lemma_1_card (hk : 2 ≤ k) (hΔ : 2 ^ (4 ^ k + 1) ≤ Δ) (hQ : Q ∈ (tritOne k).h Δ)
    (hc : Multiset.card Q = Δ) :
    ∃ P, (Δ - 2 ^ (4 ^ k) ≤ Q.count P ∧ ones k ∈ P) ∧
      ∀ P', Δ - 2 ^ (4 ^ k) ≤ Q.count P' → P' = P := by
  have hnum := freqBound_le hk
  have hpow : 2 ^ (4 ^ k + 1) = 2 * 2 ^ (4 ^ k) := by rw [pow_succ]; ring
  have hsum := Multiset.sum_count_eq_card (s := Finset.univ) (m := Q)
    (fun a _ => Finset.mem_univ a)
  have hcardS : Fintype.card (Set (Trit k)) = 2 ^ (3 ^ k) := by simp [Fintype.card_set]
  have h2 : 2 ≤ 2 ^ (3 ^ k) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (3 ^ k) := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_pow _ _ (by norm_num))
  set M := (k + 1) * 3 ^ k with hMdef
  have hM2 : 2 * M ≤ 2 ^ (4 ^ k) := le_trans (by rw [mul_comm]; exact Nat.mul_le_mul_left M h2) hnum
  have hM : M = k * 3 ^ k + 3 ^ k := by rw [hMdef]; ring
  have h3 : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
  obtain ⟨P, hP⟩ : ∃ P, M < Q.count P := by
    by_contra h
    push Not at h
    have : ∑ P ∈ Finset.univ, Q.count P ≤ ∑ _P ∈ (Finset.univ : Finset (Set (Trit k))), M :=
      Finset.sum_le_sum fun P _ => h P
    rw [Finset.sum_const, Finset.card_univ, hcardS, smul_eq_mul, hsum, hc] at this
    have : 2 ^ (3 ^ k) * M ≤ 2 ^ (4 ^ k) := by rw [mul_comm]; exact hnum
    omega
  have hrest : ∑ P' ∈ Finset.univ.erase P, Q.count P' ≤ 2 ^ (4 ^ k) := by
    calc ∑ P' ∈ Finset.univ.erase P, Q.count P' ≤ ∑ _P' ∈ Finset.univ.erase P, M := by
          refine Finset.sum_le_sum fun P' hP' => ?_
          by_contra hlt
          exact (Finset.mem_erase.1 hP').1 (freq_unique hQ hc (by omega) hP)
      _ = (Finset.univ.erase P).card * M := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 2 ^ (3 ^ k) * M := by
          gcongr
          exact (Finset.card_erase_le).trans (by rw [Finset.card_univ, hcardS])
      _ ≤ 2 ^ (4 ^ k) := by rw [mul_comm]; exact hnum
  have hcP : Δ - 2 ^ (4 ^ k) ≤ Q.count P := by
    have := Finset.add_sum_erase Finset.univ (fun P => Q.count P) (Finset.mem_univ P)
    omega
  refine ⟨P, ⟨hcP, ones_mem_of_count hQ hc (by omega)⟩, fun P' hP' =>
    freq_unique hQ hc (by omega) hP⟩

end

/-! ### The cardinality hypothesis is needed

`Problem.nodeStepMax` allows node configurations with fewer than `Δ` elements (as in §3 of the
paper, where `h(Δ)` consists of multisets of *at most* `Δ` labels). With an empty set among them,
Property A holds vacuously, and `{∅}` satisfies Properties A and B. So Lemma 1 needs
`card Q = Δ` (which holds in the paper, where `h_1(Δ)` consists of multisets `{W_1, …, W_Δ}`). -/

theorem singleton_empty_mem_h {Δ : ℕ} (hΔ : 2 ≤ Δ) :
    ({∅} : Multiset (Set (Trit k))) ∈ (tritOne k).h Δ := by
  refine ⟨⟨by simp; omega, fun _ _ => Set.subset_univ _, fun m' hm' => ?_⟩, fun Y hY Y' hY' h => ?_⟩
  · obtain ⟨a, _, ha, _, _⟩ := Multiset.rel_cons_right.1 hm'
    exact absurd ha (Set.notMem_empty a)
  · rw [Multiset.mem_singleton] at hY
    subst hY
    obtain ⟨y, hy, -⟩ := Set.exists_of_ssubset hY'
    have := h.2.2 {y} (by rw [Multiset.erase_singleton]; exact Multiset.Rel.cons hy Multiset.Rel.zero)
    have := this.1
    simp at this
    omega

/-- Lemma 1 as stated in `lemma_1` (without `card Q = Δ`) is false: `Q = {∅}`, `k = 2`. -/
theorem lemma_1_needs_card :
    ¬ ∀ {k Δ : ℕ}, 2 ≤ k → 2 ^ (4 ^ k + 1) ≤ Δ → ∀ {Q : Multiset (Set (Trit k))},
      Q ∈ (tritOne k).h Δ → ∃ P, (Δ - 2 ^ (4 ^ k) ≤ Q.count P ∧ ones k ∈ P) ∧
        ∀ P', Δ - 2 ^ (4 ^ k) ≤ Q.count P' → P' = P := by
  intro h
  obtain ⟨P, ⟨hP, -⟩, -⟩ := h (k := 2) (Δ := 2 ^ (4 ^ 2 + 1)) le_rfl le_rfl
    (singleton_empty_mem_h (by norm_num))
  have : Multiset.count P ({∅} : Multiset (Set (Trit 2))) ≤ 1 := by
    rw [Multiset.count_singleton]; split_ifs <;> simp
  norm_num at hP
  omega

end AutomaticSpeedup
