import Papers.PODC2024.DataCenterRouting.Adversarial

/-!
# Section 4: lex-max-min fairness does not provide the macro-switch abstraction

Clos network `C_n`, `n = k + 1 ≥ 3`, with the adversarial flows of `Adversarial.lean`.

* `claim_4_5`, `exists_perm_of_feasible`: if the type-1 and type-2 flows keep (at least) their
  macro-switch rates, every input switch sends all its type-2 flows through a single middle switch,
  and distinct input switches use distinct middle switches;
* `lemma_4_4`: the max-min fair allocation in `MS_n` (type 1: `1/p`, type 2: `1/n`, type 3: `1`);
* `lemma_4_6`: the lex-max-min fair allocation in `C_n` for `p = n + 1` (type 1: `1/(n+1)`,
  type 2: `1/n`, type 3: `1/n`), which is moreover unique;
* `example_4_1`: for `p = 1` the macro-switch max-min fair rates cannot be replicated by any
  routing;
* `theorem_4_2`, `theorem_4_3`.
-/

namespace Podc.DataCenterRouting

open Cslib.RateAllocation Finset

variable {k p : ℕ}

/-! ### Arithmetic and counting helpers -/

/-- If `X/p + Y/K = 1` with `p` and `K` coprime, then `Y = 0` or `Y = K`. -/
theorem eq_zero_or_eq_of_div_add_div {p K X Y : ℕ} (hp : 0 < p) (hK : 0 < K)
    (hcop : Nat.Coprime p K) (h : (X : ℝ) / p + Y / K = 1) : Y = 0 ∨ Y = K := by
  have hp' : (p : ℝ) ≠ 0 := by positivity
  have hK' : (K : ℝ) ≠ 0 := by positivity
  have h1 : ((K * X + p * Y : ℕ) : ℝ) = ((p * K : ℕ) : ℝ) := by
    push_cast
    field_simp at h
    linarith
  have h2 : K * X + p * Y = p * K := by exact_mod_cast h1
  have hdvd : K ∣ p * Y := by
    have : p * Y = K * (p - X) := by
      rw [Nat.mul_sub, Nat.mul_comm K p]; omega
    exact ⟨p - X, this⟩
  have hY : K ∣ Y := (Nat.Coprime.symm hcop).dvd_of_dvd_mul_left hdvd
  have hle : Y ≤ K := by
    by_contra hc
    push Not at hc
    have : p * K < p * Y := Nat.mul_lt_mul_of_pos_left hc hp
    omega
  obtain ⟨t, rfl⟩ := hY
  rcases Nat.lt_or_ge t 2 with ht | ht
  · interval_cases t <;> simp
  · nlinarith

/-- A sum of an indicator-weighted function is at least `c` times the number of terms. -/
theorem card_mul_le_sum_ite {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (b : ι → ℝ) (c : ℝ) (h : ∀ x, P x → c ≤ b x) :
    ((univ.filter P).card : ℝ) * c ≤ ∑ x, if P x then b x else 0 := by
  rw [← Finset.sum_filter, ← nsmul_eq_mul]
  exact Finset.card_nsmul_le_sum _ _ _ fun x hx => h x (Finset.mem_filter.1 hx).2

/-- Sum of the fiber sizes of a map into `Fin (k + 1)`. -/
theorem sum_card_fiber {ι : Type*} [Fintype ι] (g : ι → Fin (k + 1)) :
    ∑ m, ((univ.filter (fun x => g x = m)).card : ℝ) = Fintype.card ι := by
  have := Finset.card_eq_sum_card_fiberwise (f := g) (s := univ) (t := univ)
    (fun x _ => Finset.mem_univ _)
  rw [Finset.card_univ] at this
  exact_mod_cast this.symm

/-! ### Claim 4.5 -/

section Claim

variable (r : AdvFlow k p → Fin (k + 1)) (b : AdvFlow k p → ℝ)

/-- Number of type-1 flows leaving `I_{i+1}` routed through `M_{m+1}` (`x_i^m` of the paper). -/
noncomputable def cnt1 (i m : Fin (k + 1)) : ℕ :=
  (univ.filter (fun x : Fin k × Fin p => r (t1 i x.1 x.2) = m)).card

/-- Number of type-2 flows leaving `I_{i+1}` routed through `M_{m+1}` (`y_i^m` of the paper). -/
noncomputable def cnt2 (i m : Fin (k + 1)) : ℕ :=
  (univ.filter (fun y : Option (Fin k) => r (t2 i y) = m)).card

variable {r b}

/-- Under a feasible allocation in which type-1 and type-2 flows keep at least their macro-switch
rates, `x_i^m/p + y_i^m/n = 1` for all `i, m` (first step of the proof of Claim 4.5). -/
theorem cnt_eq_one (hp : 0 < p) (hb : (clos (adv k p) r).Feasible b)
    (h1 : ∀ i j c, 1 / (p : ℝ) ≤ b (t1 i j c)) (h2 : ∀ i y, 1 / (k + 1 : ℝ) ≤ b (t2 i y))
    (i m : Fin (k + 1)) :
    (cnt1 r i m : ℝ) / p + (cnt2 r i m : ℝ) / (k + 1) = 1 := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hle : ∀ m, (cnt1 r i m : ℝ) / p + (cnt2 r i m : ℝ) / (k + 1) ≤ 1 := by
    intro m
    have hload := hb.2 (.up (tor i) m)
    rw [clos_load_up, upSum_tor, clos_cap] at hload
    have e1 := card_mul_le_sum_ite (fun x : Fin k × Fin p => r (t1 i x.1 x.2) = m)
      (fun x => b (t1 i x.1 x.2)) (1 / p) fun x _ => h1 _ _ _
    have e2 := card_mul_le_sum_ite (fun y : Option (Fin k) => r (t2 i y) = m)
      (fun y => b (t2 i y)) (1 / (k + 1)) fun y _ => h2 _ _
    simp only [cnt1, cnt2]
    rw [div_eq_mul_one_div, div_eq_mul_one_div (_ : ℝ) ((k : ℝ) + 1)]
    linarith
  have hsum : ∑ m, ((cnt1 r i m : ℝ) / p + (cnt2 r i m : ℝ) / (k + 1)) = ∑ _m : Fin (k + 1), 1 := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
    simp only [cnt1, cnt2]
    rw [sum_card_fiber (fun x : Fin k × Fin p => r (t1 i x.1 x.2)),
      sum_card_fiber (fun y : Option (Fin k) => r (t2 i y))]
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_option, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    push_cast
    field_simp
  exact (Finset.sum_eq_sum_iff_of_le (fun m _ => hle m)).1 hsum m (Finset.mem_univ m)

/-- If type-1 and type-2 flows keep at least their macro-switch rates in a feasible allocation of
`C_n`, then all type-2 flows leaving `I_{i+1}` are routed through a common middle switch `σ i`,
and `σ` is a bijection (Claim 4.5, with `n ≥ 3`). -/
theorem exists_perm_of_feasible (hk : 2 ≤ k) (hp : 0 < p) (hcop : Nat.Coprime p (k + 1))
    (hb : (clos (adv k p) r).Feasible b)
    (h1 : ∀ i j c, 1 / (p : ℝ) ≤ b (t1 i j c)) (h2 : ∀ i y, 1 / (k + 1 : ℝ) ≤ b (t2 i y)) :
    ∃ σ : Fin (k + 1) → Fin (k + 1), (∀ i y, r (t2 i y) = σ i) ∧ Function.Bijective σ := by
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  -- every input switch sends all its type-2 flows through one middle switch
  have hσ : ∀ i, ∃ m, ∀ y, r (t2 i y) = m := by
    intro i
    have hsum : ∑ m, cnt2 r i m = k + 1 := by
      have := Finset.card_eq_sum_card_fiberwise (f := fun y : Option (Fin k) => r (t2 i y))
        (s := univ) (t := univ) (fun x _ => Finset.mem_univ _)
      simp only [Finset.card_univ, Fintype.card_option, Fintype.card_fin] at this
      exact this.symm
    obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := univ)
      (f := fun m => cnt2 r i m) (by rw [hsum]; omega)
    refine ⟨m, fun y => ?_⟩
    rcases eq_zero_or_eq_of_div_add_div hp (by omega) hcop
      (by push_cast; exact cnt_eq_one hp hb h1 h2 i m) with h | h
    · exact absurd h hm
    · have : univ.filter (fun y : Option (Fin k) => r (t2 i y) = m) = univ := by
        apply Finset.eq_univ_of_card
        rw [Fintype.card_option, Fintype.card_fin]; exact h
      have hy : y ∈ univ.filter (fun y : Option (Fin k) => r (t2 i y) = m) := by
        rw [this]; exact Finset.mem_univ y
      exact (Finset.mem_filter.1 hy).2
  choose σ hσ using hσ
  refine ⟨σ, hσ, ?_⟩
  -- two input switches cannot share a middle switch: `2(n-1)/n > 1`
  have hinj : Function.Injective σ := by
    intro i i' hii'
    by_contra hne
    have hload := hb.2 (.down (σ i) (torN k))
    rw [clos_load_down, downSum_torN, clos_cap] at hload
    have e1 := card_mul_le_sum_ite
      (fun x : Fin (k + 1) × Fin k => r (t2 x.1 (some x.2)) = σ i)
      (fun x => b (t2 x.1 (some x.2))) (1 / (k + 1)) fun x _ => h2 _ _
    have hcard : 2 * k ≤ (univ.filter
        (fun x : Fin (k + 1) × Fin k => r (t2 x.1 (some x.2)) = σ i)).card := by
      have hsub : ({i, i'} : Finset (Fin (k + 1))) ×ˢ (univ : Finset (Fin k)) ⊆
          univ.filter (fun x : Fin (k + 1) × Fin k => r (t2 x.1 (some x.2)) = σ i) := by
        intro x hx
        simp only [Finset.mem_product, Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hσ]
        rcases hx.1 with h | h <;> rw [h]
        exact hii'.symm
      have := Finset.card_le_card hsub
      rwa [Finset.card_product, Finset.card_pair hne, Finset.card_univ, Fintype.card_fin] at this
    have ht3 : 0 ≤ if r t3 = σ i then b t3 else 0 := by split_ifs <;> [exact hb.1 _; exact le_rfl]
    have : (2 * k : ℝ) * (1 / (k + 1)) ≤ 1 := by
      have h' := (Nat.cast_le (α := ℝ)).2 hcard
      push_cast at h'
      have := mul_le_mul_of_nonneg_right h' (le_of_lt (one_div_pos.2 hk1))
      linarith
    rw [mul_one_div, div_le_one hk1] at this
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  exact ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩

/-- Consequence of Claim 4.5: if type-1 and type-2 flows keep at least their macro-switch rates in a
feasible allocation of `C_n`, `n ≥ 3`, then the type-3 flow gets at most `1/n`. -/
theorem t3_le (hk : 2 ≤ k) (hp : 0 < p) (hcop : Nat.Coprime p (k + 1))
    (hb : (clos (adv k p) r).Feasible b)
    (h1 : ∀ i j c, 1 / (p : ℝ) ≤ b (t1 i j c)) (h2 : ∀ i y, 1 / (k + 1 : ℝ) ≤ b (t2 i y)) :
    b t3 ≤ 1 / (k + 1) := by
  obtain ⟨σ, hσ, hbij⟩ := exists_perm_of_feasible hk hp hcop hb h1 h2
  obtain ⟨i0, hi0⟩ := hbij.2 (r t3)
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have hload := hb.2 (.down (r t3) (torN k))
  rw [clos_load_down, downSum_torN, clos_cap, ite_eq_left rfl] at hload
  have e1 := card_mul_le_sum_ite
    (fun x : Fin (k + 1) × Fin k => r (t2 x.1 (some x.2)) = r t3)
    (fun x => b (t2 x.1 (some x.2))) (1 / (k + 1)) fun x _ => h2 _ _
  have hcard : k ≤ (univ.filter
      (fun x : Fin (k + 1) × Fin k => r (t2 x.1 (some x.2)) = r t3)).card := by
    have hsub : ({i0} : Finset (Fin (k + 1))) ×ˢ (univ : Finset (Fin k)) ⊆
        univ.filter (fun x : Fin (k + 1) × Fin k => r (t2 x.1 (some x.2)) = r t3) := by
      intro x hx
      simp only [Finset.mem_product, Finset.mem_singleton] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hσ, hx.1, hi0]
    have := Finset.card_le_card hsub
    rwa [Finset.card_product, Finset.card_singleton, Finset.card_univ, Fintype.card_fin,
      one_mul] at this
  have h' := (Nat.cast_le (α := ℝ)).2 hcard
  have : (k : ℝ) * (1 / (k + 1)) + b t3 ≤ 1 := by
    have := mul_le_mul_of_nonneg_right h' (le_of_lt (one_div_pos.2 hk1))
    linarith
  rw [mul_one_div] at this
  have e : (1 : ℝ) - k / (k + 1) = 1 / (k + 1) := by field_simp; ring
  linarith

/-- **Claim 4.5.** Assume that type-1 flows are offered with rate `1/(n+1)` (here `1/p`) and
type-2 flows with rate `1/n`, and that the routing `r` is feasible for them (the type-3 flow may
take any rate). Then (1) for all `i, m`, the numbers of type-1 and type-2 flows leaving `I_i` and
assigned to `M_m` are `0` and `n`, or `p` and `0`; and (2) every middle switch carries exactly
`n - 1` type-2.b flows. -/
theorem claim_4_5 (hk : 2 ≤ k) (hp : 0 < p) (hcop : Nat.Coprime p (k + 1))
    (hb : (clos (adv k p) r).Feasible b)
    (h1 : ∀ i j c, b (t1 i j c) = 1 / p) (h2 : ∀ i y, b (t2 i y) = 1 / (k + 1)) :
    (∀ i m, (cnt1 r i m = 0 ∧ cnt2 r i m = k + 1) ∨ (cnt1 r i m = p ∧ cnt2 r i m = 0)) ∧
    ∀ m, (univ.filter (fun x : Fin (k + 1) × Fin k => r (t2 x.1 (some x.2)) = m)).card = k := by
  have h1' : ∀ i j c, 1 / (p : ℝ) ≤ b (t1 i j c) := fun i j c => (h1 i j c).ge
  have h2' : ∀ i y, 1 / (k + 1 : ℝ) ≤ b (t2 i y) := fun i y => (h2 i y).ge
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  refine ⟨fun i m => ?_, fun m => ?_⟩
  · have heq := cnt_eq_one hp hb h1' h2' i m
    rcases eq_zero_or_eq_of_div_add_div hp (by omega) hcop (by push_cast; exact heq) with h | h
    · right
      refine ⟨?_, h⟩
      rw [h] at heq
      have : (cnt1 r i m : ℝ) = p := by
        field_simp at heq
        simp at heq
        rcases heq with h0 | h0
        · exact_mod_cast h0
        · have : (0 : ℝ) < k + 1 := by positivity
          linarith
      exact_mod_cast this
    · left
      refine ⟨?_, h⟩
      rw [h] at heq
      have : (cnt1 r i m : ℝ) / p = 0 := by push_cast at heq; field_simp at heq ⊢; linarith
      rw [div_eq_zero_iff] at this
      rcases this with h0 | h0
      · exact_mod_cast h0
      · exact absurd h0 hp'.ne'
  · obtain ⟨σ, hσ, hbij⟩ := exists_perm_of_feasible hk hp hcop hb h1' h2'
    obtain ⟨i0, hi0⟩ := hbij.2 m
    have : univ.filter (fun x : Fin (k + 1) × Fin k => r (t2 x.1 (some x.2)) = m) =
        ({i0} : Finset (Fin (k + 1))) ×ˢ (univ : Finset (Fin k)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hσ, Finset.mem_product,
        Finset.mem_singleton, and_true]
      constructor
      · intro h; exact hbij.1 (h.trans hi0.symm)
      · intro h; rw [h, hi0]
    rw [this, Finset.card_product, Finset.card_singleton, Finset.card_univ, Fintype.card_fin,
      one_mul]

end Claim

/-! ### Server links -/

section Servers

/-- No load beyond `1` on the server links for the allocation `advRate θ`, `θ ≤ 1`. -/
theorem advRate_srcSum_le (hp : 0 < p) {θ : ℝ} (_hθ0 : 0 ≤ θ) (hθ : θ ≤ 1) (s : Server (k + 1)) :
    (∑ f, if (adv k p).src f = s then advRate k p θ f else 0) ≤ 1 := by
  have hp' : (p : ℝ) ≠ 0 := by positivity
  obtain ⟨x, y⟩ := s
  rcases switch_cases x with ⟨i, rfl⟩ | rfl | ⟨h1, h2⟩
  · induction y using Fin.cases with
    | zero => rw [srcSum_t2]; simp; field_simp; rfl
    | succ j => rw [srcSum_t1]; simp; field_simp; rfl
  · induction y using Fin.lastCases with
    | last => rw [srcSum_t3]; simpa using hθ
    | cast j =>
      rw [srcSum_zero]
      · norm_num
      · intro f
        rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
        · simp
        · simp
        · simp [Fin.ext_iff]; omega
  · rw [srcSum_zero]
    · norm_num
    · intro f
      rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
      · exact fun h => h1 i' (congrArg Prod.fst h).symm
      · exact fun h => h1 i' (congrArg Prod.fst h).symm
      · exact fun h => h2 (congrArg Prod.fst h).symm

/-- No load beyond `1` on the server links for the allocation `advRate θ`, `θ ≤ 1`. -/
theorem advRate_dstSum_le (hp : 0 < p) {θ : ℝ} (_hθ0 : 0 ≤ θ) (hθ : θ ≤ 1) (s : Server (k + 1)) :
    (∑ f, if (adv k p).dst f = s then advRate k p θ f else 0) ≤ 1 := by
  have hp' : (p : ℝ) ≠ 0 := by positivity
  have hk : (0 : ℝ) < k + 1 := by positivity
  obtain ⟨x, y⟩ := s
  rcases switch_cases x with ⟨i, rfl⟩ | rfl | ⟨h1, h2⟩
  · induction y using Fin.cases with
    | zero => rw [dstSum_t2a]; simp only [advRate_t2]; rw [div_le_one hk]; linarith
    | succ j => rw [dstSum_t1]; simp; field_simp; rfl
  · induction y using Fin.lastCases with
    | last => rw [dstSum_t3]; simpa using hθ
    | cast j => rw [dstSum_t2b]; simp; field_simp; rfl
  · rw [dstSum_zero]
    · norm_num
    · intro f
      rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
      · exact fun h => h1 i' (congrArg Prod.fst h).symm
      · cases y with
        | none => exact fun h => h1 i' (congrArg Prod.fst h).symm
        | some j => exact fun h => h2 (congrArg Prod.fst h).symm
      · exact fun h => h2 (congrArg Prod.fst h).symm

theorem advRate_nonneg {θ : ℝ} (hθ0 : 0 ≤ θ) (f : AdvFlow k p) : 0 ≤ advRate k p θ f := by
  rcases f.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl <;> simp [hθ0] <;> positivity

/-- In both the macro-switch and the Clos network, a type-1 flow has its source link as a
bottleneck under `advRate θ`. -/
theorem srcBottleneck_t1 (N : Network (AdvFlow k p) (Link (k + 1))) (hp : 0 < p) (θ : ℝ)
    (hmem : ∀ g s, Link.srcLink s ∈ N.path g ↔ (adv k p).src g = s)
    (hload : ∀ b s, N.load b (.srcLink s) = ∑ f, if (adv k p).src f = s then b f else 0)
    (hcap : ∀ s, N.cap (.srcLink s) = 1) (i : Fin (k + 1)) (j : Fin k) (c : Fin p) :
    N.IsBottleneck (advRate k p θ) (t1 i j c) (.srcLink (tor i, j.succ)) := by
  have hp' : (p : ℝ) ≠ 0 := by positivity
  refine ⟨(hmem _ _).2 rfl, ?_, fun g hg => ?_⟩
  · rw [hload, srcSum_t1, hcap]; simp; field_simp
  · rw [hmem] at hg
    rcases g.cases with ⟨i', j', c', rfl⟩ | ⟨i', y, rfl⟩ | rfl
    · simp
    · simp [(Fin.succ_ne_zero j).symm] at hg
    · simp at hg

/-- In both the macro-switch and the Clos network, a type-2 flow has its source link as a
bottleneck under `advRate θ`. -/
theorem srcBottleneck_t2 (N : Network (AdvFlow k p) (Link (k + 1))) (θ : ℝ)
    (hmem : ∀ g s, Link.srcLink s ∈ N.path g ↔ (adv k p).src g = s)
    (hload : ∀ b s, N.load b (.srcLink s) = ∑ f, if (adv k p).src f = s then b f else 0)
    (hcap : ∀ s, N.cap (.srcLink s) = 1) (i : Fin (k + 1)) (y : Option (Fin k)) :
    N.IsBottleneck (advRate k p θ) (t2 i y) (.srcLink (tor i, 0)) := by
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  refine ⟨(hmem _ _).2 rfl, ?_, fun g hg => ?_⟩
  · rw [hload, srcSum_t2, hcap]; simp; field_simp
  · rw [hmem] at hg
    rcases g.cases with ⟨i', j', c', rfl⟩ | ⟨i', y', rfl⟩ | rfl
    · simp [Fin.succ_ne_zero] at hg
    · simp
    · simp at hg

theorem macroSwitch_mem_src (g : AdvFlow k p) (s : Server (k + 1)) :
    Link.srcLink s ∈ (macroSwitch (adv k p)).path g ↔ (adv k p).src g = s := by
  rw [mem_macroSwitch_path]; simp [eq_comm]

theorem clos_mem_src (r : AdvFlow k p → Fin (k + 1)) (g : AdvFlow k p) (s : Server (k + 1)) :
    Link.srcLink s ∈ (clos (adv k p) r).path g ↔ (adv k p).src g = s := by
  rw [mem_clos_path]; simp [eq_comm]

end Servers

/-! ### Lemma 4.4: the max-min fair allocation in the macro-switch -/

/-- **Lemma 4.4** (for any number `p ≥ 1` of copies of the type-1 flows; the paper's case is
`p = n + 1`, Example 4.1 is `p = 1`). In the max-min fair allocation in `MS_n` of the adversarial
flows, type-1 flows get `1/p`, type-2 flows get `1/n` and the type-3 flow gets `1`. -/
theorem lemma_4_4 (hp : 0 < p) : (macroSwitch (adv k p)).IsMaxMinFair (advRate k p 1) := by
  apply Network.isMaxMinFair_of_hasBottlenecks
  · refine ⟨advRate_nonneg zero_le_one, fun ℓ => ?_⟩
    cases ℓ with
    | srcLink s =>
      rw [macroSwitch_load_srcLink]; exact advRate_srcSum_le hp zero_le_one le_rfl s
    | dstLink s =>
      rw [macroSwitch_load_dstLink]; exact advRate_dstSum_le hp zero_le_one le_rfl s
    | up i m => rw [macroSwitch_load_up]; simp
    | down m o => rw [macroSwitch_load_down]; simp
  · intro f
    rcases f.cases with ⟨i, j, c, rfl⟩ | ⟨i, y, rfl⟩ | rfl
    · exact ⟨_, srcBottleneck_t1 _ hp 1 macroSwitch_mem_src
        (macroSwitch_load_srcLink _) (fun _ => rfl) i j c⟩
    · exact ⟨_, srcBottleneck_t2 _ 1 macroSwitch_mem_src
        (macroSwitch_load_srcLink _) (fun _ => rfl) i y⟩
    · refine ⟨.srcLink (torN k, Fin.last k), (macroSwitch_mem_src _ _).2 rfl, ?_, fun g hg => ?_⟩
      · rw [macroSwitch_load_srcLink, srcSum_t3]; rfl
      · rw [macroSwitch_mem_src] at hg
        rcases g.cases with ⟨i', j', c', rfl⟩ | ⟨i', y', rfl⟩ | rfl
        · simp at hg
        · simp at hg
        · exact le_rfl

/-! ### Example 4.1 and Theorem 4.2 -/

/-- **Example 4.1** (generalized to `n ≥ 3`, as in the proof of Theorem 4.2). With one copy of each
type-1 flow, the max-min fair macro-switch rates cannot be replicated in `C_n`: no routing makes
them feasible. -/
theorem example_4_1 (hk : 2 ≤ k) (r : AdvFlow k 1 → Fin (k + 1)) :
    ¬ (clos (adv k 1) r).Feasible (advRate k 1 1) := by
  intro hb
  have := t3_le hk one_pos (Nat.coprime_one_left _) hb (fun _ _ _ => by simp)
    (fun _ _ => le_rfl)
  simp only [advRate_t3] at this
  rw [le_div_iff₀ (by positivity)] at this
  have : (2 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- **Theorem 4.2.** For every `n ≥ 3` there is a collection of flows in `C_n` such that the sorted
vector of the max-min fair allocation in `MS_n` is strictly greater than that of the max-min fair
allocation of every routing — in particular `a^MmF↑ ≻ a^{L-MmF}↑`. (Flows of Example 4.1.) -/
theorem theorem_4_2 (n : ℕ) (hn : 3 ≤ n) :
    ∃ (F : Type) (_ : Fintype F) (fl : Flows n F) (aMS : F → ℝ),
      (macroSwitch fl).IsMaxMinFair aMS ∧
      ∀ r a, (clos fl r).IsMaxMinFair a → sortedRates a < sortedRates aMS := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨AdvFlow k 1, inferInstance, adv k 1, advRate k 1 1, lemma_4_4 one_pos,
    fun r a ha => ?_⟩
  refine (lemma_4_4 one_pos).sortedRates_lt (Feasible.toMacroSwitch _ ha.1) fun h => ?_
  rw [h] at ha
  exact example_4_1 (by omega) r ha.1

/-! ### Lemma 4.6: the lex-max-min fair allocation in the Clos network -/

section LexMaxMinFair

variable (k p) in
/-- The routing of Lemma 4.6 (Figure 3b): type-1 flows leaving `I_{i+1}` towards server `j + 2`
use `M_{(i.succAbove j)+1}` (all middle switches except `M_{i+1}`, one per server — the paper uses
`M_{k+1}` with `k = i + j - 2 mod n`, an equivalent choice), type-2 flows leaving `I_{i+1}` use
`M_{i+1}`, and the type-3 flow uses `M_n`. -/
def rStar : AdvFlow k p → Fin (k + 1)
  | .inl (i, j, _) => i.succAbove j
  | .inr (.inl (i, _)) => i
  | .inr (.inr _) => Fin.last k

theorem sum_succAbove_ite (i m : Fin (k + 1)) (c : ℝ) :
    (∑ j : Fin k, if i.succAbove j = m then c else 0) = if m = i then 0 else c := by
  split_ifs with h
  · subst h
    exact Finset.sum_eq_zero fun j _ => ite_eq_right (Fin.succAbove_ne m j)
  · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq h
    rw [Finset.sum_eq_single z]
    · simp [hz]
    · intro j _ hj
      rw [ite_eq_right]
      intro h'
      exact hj (Fin.succAbove_right_injective (h'.trans hz.symm))
    · simp

theorem sum_t1_rStar (hp : 0 < p) {θ : ℝ} (i m : Fin (k + 1)) :
    (∑ x : Fin k × Fin p, if rStar k p (t1 i x.1 x.2) = m then advRate k p θ (t1 i x.1 x.2)
      else 0) = if m = i then 0 else 1 := by
  have hp' : (p : ℝ) ≠ 0 := by positivity
  rw [Fintype.sum_prod_type, ← sum_succAbove_ite i m 1]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [rStar, advRate_t1]
  split_ifs with h <;> simp [h, hp']

theorem sum_t2_rStar_up {θ : ℝ} (i m : Fin (k + 1)) :
    (∑ y, if rStar k p (t2 i y) = m then advRate k p θ (t2 i y) else 0) =
      if i = m then 1 else 0 := by
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  simp only [rStar, advRate_t2]
  split_ifs with h <;> simp [h]
  field_simp

theorem sum_t2b_rStar {θ : ℝ} (m : Fin (k + 1)) :
    (∑ x : Fin (k + 1) × Fin k, if rStar k p (t2 x.1 (some x.2)) = m then
      advRate k p θ (t2 x.1 (some x.2)) else 0) = k * (1 / (k + 1)) := by
  rw [Fintype.sum_prod_type]
  simp only [rStar, advRate_t2]
  rw [Finset.sum_eq_single m]
  · simp
  · intro i _ hi; simp [hi]
  · simp

/-- The allocation `advRate θ`, `0 ≤ θ ≤ 1/n`, is feasible in `C_n` under the routing `rStar`. -/
theorem rStar_feasible (hp : 0 < p) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / (k + 1)) :
    (clos (adv k p) (rStar k p)).Feasible (advRate k p θ) := by
  have hp' : (p : ℝ) ≠ 0 := by positivity
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hθ1 : θ ≤ 1 := hθ.trans (by rw [div_le_one hk]; linarith)
  refine ⟨advRate_nonneg hθ0, fun ℓ => ?_⟩
  rw [clos_cap]
  cases ℓ with
  | srcLink s => rw [clos_load_srcLink]; exact advRate_srcSum_le hp hθ0 hθ1 s
  | dstLink s => rw [clos_load_dstLink]; exact advRate_dstSum_le hp hθ0 hθ1 s
  | up x m =>
    rw [clos_load_up]
    rcases switch_cases x with ⟨i, rfl⟩ | rfl | ⟨h1, h2⟩
    · rw [upSum_tor, sum_t1_rStar hp, sum_t2_rStar_up]
      by_cases h : m = i
      · subst h; simp
      · simp [h, Ne.symm h]
    · rw [upSum_torN]
      split_ifs <;> simp [hθ1]
    · rw [upSum_zero _ _ _ _ h1 h2]; norm_num
  | down m x =>
    rw [clos_load_down]
    rcases switch_cases x with ⟨i, rfl⟩ | rfl | ⟨h1, h2⟩
    · rw [downSum_tor, sum_t1_rStar hp]
      rw [show rStar k p (t2 i none) = i from rfl, advRate_t2]
      by_cases h : m = i
      · subst h
        rw [ite_eq_left rfl, ite_eq_left rfl, zero_add, div_le_one hk]; linarith
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
        norm_num
    · rw [downSum_torN, sum_t2b_rStar]
      have : (k : ℝ) * (1 / (k + 1)) + θ ≤ 1 := by
        rw [mul_one_div]
        have e : (1 : ℝ) - k / (k + 1) = 1 / (k + 1) := by field_simp; ring
        linarith
      rw [show rStar k p t3 = Fin.last k from rfl, advRate_t3]
      split_ifs <;> linarith
    · rw [downSum_zero _ _ _ _ h1 h2]; norm_num

/-- A sum bounded by `|ι| v` with a term above `v` has a term below `v`. -/
theorem exists_lt_of_sum_le {ι : Type*} [Fintype ι] (b : ι → ℝ) (v : ℝ)
    (h : ∑ x, b x ≤ Fintype.card ι * v) (x0 : ι) (hx0 : v < b x0) : ∃ x, b x < v := by
  by_contra hc
  push Not at hc
  have : ∑ _x : ι, v < ∑ x, b x := Finset.sum_lt_sum (fun x _ => hc x) ⟨x0, mem_univ _, hx0⟩
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
  linarith

variable (k) in
/-- The posited lex-max-min fair allocation `a*` of Lemma 4.6 (`p = n + 1` copies of each type-1
flow): type 1 gets `1/(n+1)`, type 2 gets `1/n`, type 3 gets `1/n`. -/
noncomputable abbrev aStar : AdvFlow k (k + 2) → ℝ := advRate k (k + 2) (1 / (k + 1))

theorem aStar_le (g : AdvFlow k (k + 2)) : aStar k g ≤ 1 / (k + 1) := by
  rcases g.cases with ⟨i, j, c, rfl⟩ | ⟨i, y, rfl⟩ | rfl
  · simp only [advRate_t1]; push_cast
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · simp
  · simp

theorem coprime_k2 : Nat.Coprime (k + 2) (k + 1) := by
  rw [show k + 2 = 1 + (k + 1) by ring, Nat.coprime_add_self_left]
  exact Nat.coprime_one_left _

/-- Step 2 of the proof of Lemma 4.6, in the form of the leximin criterion: against every
allocation `b` that is feasible in `C_n` for **some** routing, every flow gaining with respect to
`a*` is compensated by a flow of no larger `a*`-rate losing with respect to `a*`. -/
theorem aStar_criterion (hk : 2 ≤ k) {r : AdvFlow k (k + 2) → Fin (k + 1)}
    {b : AdvFlow k (k + 2) → ℝ} (hb : (clos (adv k (k + 2)) r).Feasible b) (f : AdvFlow k (k + 2))
    (hf : aStar k f < b f) : ∃ g, aStar k g ≤ aStar k f ∧ b g < aStar k g := by
  rcases f.cases with ⟨i, j, c, rfl⟩ | ⟨i, y, rfl⟩ | rfl
  · -- Case 1, type 1: the source link `s_i^j I_i` is shared with `n` other type-1 flows
    have hload := hb.2 (.srcLink (tor i, j.succ))
    rw [clos_load_srcLink, srcSum_t1, clos_cap] at hload
    obtain ⟨c', hc'⟩ := exists_lt_of_sum_le (fun c => b (t1 i j c)) (1 / ((k + 2 : ℕ) : ℝ))
      (by rw [Fintype.card_fin]; field_simp; exact hload) c (by simpa using hf)
    exact ⟨t1 i j c', le_rfl, by simpa using hc'⟩
  · -- Case 1, type 2: the source link `s_i^1 I_i` is shared with `n - 1` other type-2 flows
    have hload := hb.2 (.srcLink (tor i, 0))
    rw [clos_load_srcLink, srcSum_t2, clos_cap] at hload
    obtain ⟨y', hy'⟩ := exists_lt_of_sum_le (fun y => b (t2 i y)) (1 / ((k : ℝ) + 1))
      (by rw [Fintype.card_option, Fintype.card_fin]; push_cast; field_simp; exact hload) y
      (by simpa using hf)
    exact ⟨t2 i y', le_rfl, by simpa using hy'⟩
  · -- Case 2, type 3: by Claim 4.5 the type-3 flow cannot exceed `1/n` unless a type-1 or
    -- type-2 flow drops below its macro-switch rate
    by_contra H
    push Not at H
    have h1 : ∀ i j c, 1 / ((k + 2 : ℕ) : ℝ) ≤ b (t1 i j c) := fun i j c => by
      have := H (t1 i j c) (aStar_le _)
      simpa using this
    have h2 : ∀ i y, 1 / (k + 1 : ℝ) ≤ b (t2 i y) := fun i y => by
      have := H (t2 i y) (aStar_le _)
      simpa using this
    have := t3_le hk (by omega) coprime_k2 hb h1 h2
    have hf' : 1 / (k + 1 : ℝ) < b t3 := by simpa using hf
    linarith

/-- Step 1 of the proof of Lemma 4.6: `a*` is the max-min fair allocation for the routing
`rStar`. -/
theorem aStar_isMaxMinFair : (clos (adv k (k + 2)) (rStar k (k + 2))).IsMaxMinFair (aStar k) := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  apply Network.isMaxMinFair_of_hasBottlenecks
  · exact rStar_feasible (by omega) (by positivity) le_rfl
  · intro f
    rcases f.cases with ⟨i, j, c, rfl⟩ | ⟨i, y, rfl⟩ | rfl
    · exact ⟨_, srcBottleneck_t1 (clos (adv k (k + 2)) (rStar k (k + 2))) (by omega)
        (1 / (k + 1)) (clos_mem_src _)
        (fun b s => clos_load_srcLink (adv k (k + 2)) b (rStar k (k + 2)) s) (fun _ => rfl) i j c⟩
    · exact ⟨_, srcBottleneck_t2 (clos (adv k (k + 2)) (rStar k (k + 2))) (1 / (k + 1))
        (clos_mem_src _)
        (fun b s => clos_load_srcLink (adv k (k + 2)) b (rStar k (k + 2)) s) (fun _ => rfl) i y⟩
    · -- the type-3 flow is bottlenecked on `M_n O_{n+1}`, shared with `n - 1` type-2.b flows
      refine ⟨.down (Fin.last k) (torN k), ?_, ?_, fun g _ => by simpa using aStar_le g⟩
      · rw [mem_clos_path]; right; right; left; rfl
      · rw [clos_load_down, downSum_torN, sum_t2b_rStar,
          show rStar k (k + 2) t3 = Fin.last k from rfl, ite_eq_left rfl,
          show aStar k t3 = 1 / (k + 1) from rfl, clos_cap]
        field_simp

/-- **Lemma 4.6.** For the adversarial flows of Theorem 4.3 (`p = n + 1`), `a*` (type 1:
`1/(n+1)`, type 2: `1/n`, type 3: `1/n`) is a lex-max-min fair allocation in `C_n` (for the routing
`rStar`), and every lex-max-min fair allocation (for any routing) is equal to `a*`. -/
theorem lemma_4_6 (hk : 2 ≤ k) :
    IsLexMaxMinFair (adv k (k + 2)) (rStar k (k + 2)) (aStar k) ∧
    ∀ r a, IsLexMaxMinFair (adv k (k + 2)) r a → a = aStar k := by
  refine ⟨⟨aStar_isMaxMinFair, fun r' a' ha' => ?_⟩, fun r a ha => ?_⟩
  · exact sortedRates_le_of_forall (aStar_criterion hk ha'.1)
  · by_contra hne
    have hlt := sortedRates_lt_of_forall (Ne.symm hne) (aStar_criterion hk ha.1.1)
    exact absurd (ha.2 _ _ aStar_isMaxMinFair) (not_le.2 hlt)

end LexMaxMinFair

/-! ### Theorem 4.3 -/

/-- **Theorem 4.3.** For every `n ≥ 3` there is a collection `F` of flows in `C_n` and a flow
`f ∈ F` such that `a^{L-MmF}(f) = (1/n) a^MmF(f)`: a lex-max-min fair allocation exists, and every
lex-max-min fair allocation gives `f` (the type-3 flow) exactly `1/n` of its rate in the max-min
fair allocation of the macro-switch (Lemmas 4.4 and 4.6). -/
theorem theorem_4_3 (n : ℕ) (hn : 3 ≤ n) :
    ∃ (F : Type) (_ : Fintype F) (fl : Flows n F) (f : F) (aMS : F → ℝ),
      (macroSwitch fl).IsMaxMinFair aMS ∧ (∃ r a, IsLexMaxMinFair fl r a) ∧
      ∀ r a, IsLexMaxMinFair fl r a → a f = 1 / n * aMS f := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨AdvFlow k (k + 2), inferInstance, adv k (k + 2), t3, advRate k (k + 2) 1,
    lemma_4_4 (by omega), ⟨_, _, (lemma_4_6 (by omega)).1⟩, fun r a ha => ?_⟩
  rw [(lemma_4_6 (by omega)).2 r a ha]
  simp

/-- **Theorem 4.2** (with the flows of Theorem 4.3, which also exhibit a lex-max-min fair
allocation): `a^MmF↑ ≻ a^{L-MmF}↑`. -/
theorem theorem_4_2' (n : ℕ) (hn : 3 ≤ n) :
    ∃ (F : Type) (_ : Fintype F) (fl : Flows n F) (aMS : F → ℝ),
      (macroSwitch fl).IsMaxMinFair aMS ∧ (∃ r a, IsLexMaxMinFair fl r a) ∧
      ∀ r a, IsLexMaxMinFair fl r a → sortedRates a < sortedRates aMS := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  refine ⟨AdvFlow k (k + 2), inferInstance, adv k (k + 2), advRate k (k + 2) 1,
    lemma_4_4 (by omega), ⟨_, _, (lemma_4_6 (by omega)).1⟩, fun r a ha => ?_⟩
  refine (lemma_4_4 (by omega)).sortedRates_lt (Feasible.toMacroSwitch _ ha.1.1) fun h => ?_
  have h3 := congrFun ((lemma_4_6 (by omega)).2 r a ha) t3
  rw [h] at h3
  simp only [advRate_t3] at h3
  have h2 : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
  rw [eq_div_iff (by positivity)] at h3
  linarith

end Podc.DataCenterRouting
