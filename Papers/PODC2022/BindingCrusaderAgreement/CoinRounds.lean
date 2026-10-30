import Papers.PODC2022.BindingCrusaderAgreement.Framework

/-!
# Expected number of rounds of Algorithm 1 (Theorems 3.1 and 3.3: "4 rounds in expectation")

Abraham, Ben-David, Yandamuri, PODC 2022, proof of Theorem 3.1 ("Termination").

The termination argument: by binding, before the coin of round `r` is revealed the adversary is
bound to a value `b_r` that no party's BCA returns negated; the value can only depend on the
coins of rounds `< r` (unpredictability: the coin of round `r` is revealed after the first
non-faulty party finished its BCA). We model the adversary's binding choices as a strategy
`β : List Bool → Bool` (coins so far ↦ bound value), so a deterministic adaptive adversary; a
strong coin gives independent uniform coins.

* `Hit β l`: in the coin prefix `l` there are rounds `r < r'` with `l[r] = β (l.take r)` (success:
  everybody starts round `r + 1` with `l[r]`, `binding_step`) and `l[r'] = l[r]` (then everybody
  commits in round `r'`, `commit_after_binding`). `hit_commits`: in every run whose binding
  values follow `β`, `Hit` on the first `k` coins implies that in some round `r' < k` every party
  finishing round `r'` commits.
* `card_not_hit_le`: at most `k + 1` of the `2^k` coin prefixes of length `k` are not hits, so
  with a fair strong coin no round `< k` makes everybody commit with probability at most
  `(k + 1) / 2^k`; `tsum_succ_div_two_pow`: `∑ (k + 1) / 2^k = 4`, the paper's bound of 4 expected
  rounds (via `E[T] = ∑_k P(T > k)`), and the probability of never terminating is `0`.

The probability-space formulation itself (`E[T] = ∑ P(T > k)`, independence) is not formalized:
we stop at the counting statement.
-/

namespace Podc.BindingCrusaderAgreement.Alg1

/-- The combinatorial event "a successful round followed by a round with the same coin". -/
def Hit : (List Bool → Bool) → List Bool → Prop
  | _, [] => False
  | β, c :: cs => (c = β [] ∧ c ∈ cs) ∨ Hit (fun h => β (c :: h)) cs

/-- Explicit form of `Hit`. -/
theorem Hit.exists {β : List Bool → Bool} {l : List Bool} (h : Hit β l) :
    ∃ r r', r < r' ∧ r' < l.length ∧ l.getD r false = β (l.take r) ∧
      l.getD r' false = l.getD r false := by
  induction l generalizing β with
  | nil => exact h.elim
  | cons c cs ih =>
    rcases h with ⟨hc, hmem⟩ | h
    · obtain ⟨i, hi, hci⟩ := List.getElem_of_mem hmem
      refine ⟨0, i + 1, by omega, by simp [hi], by simpa using hc, ?_⟩
      simp [List.getD_eq_getElem?_getD, hi, hci]
    · obtain ⟨r, r', hrr, hr', h1, h2⟩ := ih h
      refine ⟨r + 1, r' + 1, by omega, by simp [hr'], ?_, ?_⟩
      · simpa using h1
      · simpa using h2

/-- The coins of rounds `< r`. -/
def pre (c : ℕ → Bool) (r : ℕ) : List Bool := List.ofFn fun i : Fin r => c i

theorem pre_getD {c : ℕ → Bool} {k r : ℕ} (hr : r < k) : (pre c k).getD r false = c r := by
  simp [pre, List.getD_eq_getElem?_getD, hr]

theorem pre_take {c : ℕ → Bool} {k r : ℕ} (hr : r ≤ k) : (pre c k).take r = pre c r := by
  apply List.ext_getElem
  · simp [pre, hr]
  · intro i h1 h2
    simp [pre]

/-- In a run whose binding values follow the strategy `β` (no party's BCA of round `r` returns
the negation of `β` applied to the earlier coins), a hit within the first `k` coins makes every
party finishing some round `r' < k` commit in it. -/
theorem hit_commits {P : Type*} {R : Run P} (hR : R.BCA) {β : List Bool → Bool}
    (hβ : ∀ r, ∀ p ∈ R.Dec r, R.val r p ≠ some (!β (pre R.coin r))) {k : ℕ}
    (hk : Hit β (pre R.coin k)) : ∃ r' < k, ∃ b, ∀ p ∈ R.Dec r', R.Commits r' p b := by
  obtain ⟨r, r', hrr, hr', h1, h2⟩ := hk.exists
  have hlen : (pre R.coin k).length = k := by simp [pre]
  rw [hlen] at hr'
  rw [pre_getD hr', pre_getD (by omega)] at h2
  rw [pre_getD (by omega), pre_take (by omega)] at h1
  exact ⟨r', hr', R.coin r, commit_after_binding hR (h1 ▸ hβ r) rfl hrr h2⟩

open Classical in
/-- At most `k + 1` coin prefixes of length `k` are not hits, whatever the strategy. -/
theorem card_not_hit_le (k : ℕ) : ∀ β : List Bool → Bool,
    (Finset.univ.filter fun d : Fin k → Bool => ¬ Hit β (List.ofFn d)).card ≤ k + 1 := by
  induction k with
  | zero => intro β; exact (Finset.card_le_univ _).trans (le_of_eq (by simp))
  | succ k ih =>
    intro β
    -- split according to the first coin
    have hsplit : (Finset.univ.filter fun d : Fin (k + 1) → Bool => ¬ Hit β (List.ofFn d)) ⊆
        ((Finset.univ.filter fun e : Fin k → Bool => (β []) ∉ List.ofFn e).image
            (fun e : Fin k → Bool => (Fin.cons (β []) e : Fin (k + 1) → Bool))) ∪
          ((Finset.univ.filter fun e : Fin k → Bool =>
            ¬ Hit (fun h => β ((!β []) :: h)) (List.ofFn e)).image
            (fun e : Fin k → Bool => (Fin.cons (!β []) e : Fin (k + 1) → Bool))) := by
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.ofFn_succ] at hd
      have hd' : ¬ Hit β (d 0 :: List.ofFn (Fin.tail d)) := hd
      simp only [Hit, not_or, not_and] at hd'
      have hcons : d = Fin.cons (d 0) (Fin.tail d) := (Fin.cons_self_tail d).symm
      by_cases h0 : d 0 = β []
      · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨Fin.tail d, ?_, ?_⟩)
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← h0]; exact hd'.1 h0
        · rw [hcons, h0]; rfl
      · have h0' : d 0 = !β [] := by
          revert h0; generalize d 0 = u; generalize β [] = z; cases u <;> cases z <;> simp
        refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨Fin.tail d, ?_, ?_⟩)
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← h0']; exact hd'.2
        · rw [hcons, h0']; rfl
    refine (Finset.card_le_card hsplit).trans ((Finset.card_union_le _ _).trans ?_)
    have h1 : ((Finset.univ.filter fun e : Fin k → Bool => (β []) ∉ List.ofFn e).image
        (fun e : Fin k → Bool => (Fin.cons (β []) e : Fin (k + 1) → Bool))).card ≤ 1 := by
      refine Finset.card_image_le.trans (Finset.card_le_one.2 fun a ha b hb => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_ofFn] at ha hb
      funext i
      have hai : a i ≠ β [] := fun h => ha ⟨i, h⟩
      have hbi : b i ≠ β [] := fun h => hb ⟨i, h⟩
      revert hai hbi
      generalize a i = u
      generalize b i = w
      generalize β [] = z
      cases u <;> cases w <;> cases z <;> simp
    have h2 := (Finset.card_image_le
      (f := fun e : Fin k → Bool => (Fin.cons (!β []) e : Fin (k + 1) → Bool))).trans
      (ih (fun h => β ((!β []) :: h)))
    omega

/-- `∑ₖ (k + 1) / 2^k = 4`: the bound of 4 expected rounds. -/
theorem tsum_succ_div_two_pow : ∑' k : ℕ, ((k : ℝ) + 1) / 2 ^ k = 4 := by
  have h1 : ∑' k : ℕ, (k : ℝ) * (1 / 2) ^ k = 2 := by
    rw [tsum_coe_mul_geometric_of_norm_lt_one (by norm_num)]
    norm_num
  have h2 : ∑' k : ℕ, ((1 : ℝ) / 2) ^ k = 2 := tsum_geometric_two
  have hs1 : Summable fun k : ℕ => (k : ℝ) * (1 / 2) ^ k :=
    (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := 1 / 2) (by norm_num)).congr
      fun k => by simp
  have hs2 : Summable fun k : ℕ => ((1 : ℝ) / 2) ^ k := summable_geometric_two
  have : (fun k : ℕ => ((k : ℝ) + 1) / 2 ^ k) =
      fun k : ℕ => (k : ℝ) * (1 / 2) ^ k + ((1 : ℝ) / 2) ^ k := by
    funext k
    rw [div_pow, one_pow]
    ring
  rw [this, hs1.tsum_add hs2, h1, h2]
  norm_num


open Classical in
/-- Theorem 3.1 / 3.3, expected rounds, counting form. Let the adversary be deterministic, so
that the run is a function `R c` of the coin sequence `c`, with binding values given by a
strategy `β` of the earlier coins. Then among the `2^k` coin prefixes of length `k`, at most
`k + 1` leave open that no round `< k` makes every finishing party commit. With a fair strong
coin: `P(T > k) ≤ (k + 1) / 2^k`, hence `E[T] ≤ ∑ (k + 1) / 2^k = 4` rounds
(`tsum_succ_div_two_pow`). -/
theorem rounds_count {P : Type*} (R : (ℕ → Bool) → Run P) (hcoin : ∀ c, (R c).coin = c)
    (hR : ∀ c, (R c).BCA) (β : List Bool → Bool)
    (hβ : ∀ c r, ∀ p ∈ (R c).Dec r, (R c).val r p ≠ some (!β (pre c r))) (k : ℕ) :
    (Finset.univ.filter fun d : Fin k → Bool => ¬ ∀ c, pre c k = List.ofFn d →
      ∃ r' < k, ∃ b, ∀ p ∈ (R c).Dec r', (R c).Commits r' p b).card ≤ k + 1 := by
  refine (Finset.card_le_card fun d hd => ?_).trans (card_not_hit_le k β)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
  intro hhit
  apply hd
  intro c hc
  have hβ' : ∀ r, ∀ p ∈ (R c).Dec r, (R c).val r p ≠ some (!β (pre (R c).coin r)) := by
    rw [hcoin c]; exact hβ c
  exact hit_commits (hR c) hβ' (by rw [hcoin c, hc]; exact hhit)

end Podc.BindingCrusaderAgreement.Alg1
