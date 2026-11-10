import Papers.PODC2012.OrderPreservingByzRenaming.Alg5

/-!
# The id selection phase of Algorithm 5 (Lemmas 27–30, Lemma 40's count)

These lemmas are true; they are stated for the states `run` of Algorithm 5 (`Alg5.stateOf_hist`
identifies them with the states of the honest processes in a `LockStep` run). `F` is the set of
Byzantine processes, `f = |F| ≤ t`.
-/

namespace Podc.OrderPreservingByzRenaming.Alg5

variable {n t : ℕ} {sel : ℕ → List ℚ → List ℚ} {F : Finset (Fin n)} {x : Fin n → ℕ}
  {adv : ℕ → Fin n → Fin n → Option Msg}

/-- Ids received by `p` in Round 1. -/
lemma run_one_ids {p : Fin n} (hp : p ∉ F) :
    (run n t sel F x adv 1 p).ids =
      Finset.univ.biUnion fun j => if j ∈ F then identOf (adv 0 j p) else {x j} := by
  show (step n t sel 0 {} _).ids = _
  simp only [step]
  congr 1; funext j
  by_cases hj : j = p
  · subst hj; simp [hp, out, identOf]
  · by_cases hjF : j ∈ F <;> simp [hj, hjF, out, identOf]

/-- The Round-3 candidates of `p` (ids echoed `≥ n - t` times in Round 2). -/
lemma run_two_rdy {p : Fin n} (hp : p ∉ F) :
    (run n t sel F x adv 2 p).rdy =
      atLeast n (fun j => if j ∈ F then echoOf (adv 1 j p) else (run n t sel F x adv 1 j).ids)
        (n - t) := by
  show (step n t sel 1 (run n t sel F x adv 1 p) _).rdy = _
  simp only [step]
  congr 1; funext j
  by_cases hj : j = p
  · subst hj; simp [hp, out, echoOf]
  · by_cases hjF : j ∈ F <;> simp [hj, hjF, out, echoOf]

/-- The Ready sets received by `p` in Round 3. -/
def readySets (F : Finset (Fin n)) (x : Fin n → ℕ) (adv : ℕ → Fin n → Fin n → Option Msg) (p : Fin n) :
    Fin n → Finset ℕ :=
  fun j => if j ∈ F then readyOf (adv 2 j p) else (run n t sel F x adv 2 j).rdy

lemma run_three {p : Fin n} (hp : p ∉ F) :
    (run n t sel F x adv 3 p).timely = atLeast n (readySets (t := t) (sel := sel) F x adv p) (n - t) ∧
    (run n t sel F x adv 3 p).acc = atLeast n (readySets (t := t) (sel := sel) F x adv p) (n - 2 * t) := by
  have h : (fun j => readyOf (if j = p then out (x p) (run n t sel F x adv 2 p) 2
      else if j ∈ F then adv 2 j p else out (x j) (run n t sel F x adv 2 j) 2)) =
      readySets (t := t) (sel := sel) F x adv p := by
    funext j
    by_cases hj : j = p
    · subst hj; simp [readySets, hp, out, readyOf]
    · by_cases hjF : j ∈ F <;> simp [readySets, hj, hjF, out, readyOf]
  show (step n t sel 2 (run n t sel F x adv 2 p) _).timely = _ ∧
    (step n t sel 2 (run n t sel F x adv 2 p) _).acc = _
  simp only [step]
  exact ⟨congrArg (atLeast n · (n - t)) h, congrArg (atLeast n · (n - 2 * t)) h⟩

/-! ### Counting -/

/-- The honest processes. -/
def Hon (F : Finset (Fin n)) : Finset (Fin n) := Finset.univ.filter (· ∉ F)

lemma card_Hon (F : Finset (Fin n)) : (Hon F).card = n - F.card := by
  have : Hon F = Fᶜ := by ext; simp [Hon]
  rw [this, Finset.card_compl, Fintype.card_fin]

/-- Counting a value over links: at least the honest count, at most the honest count plus `|F|`. -/
lemma cnt_bounds (E A : Fin n → Finset ℕ) (hEA : ∀ j ∉ F, E j = A j) (v : ℕ) :
    ((Hon F).filter fun j => v ∈ A j).card ≤ cnt n E v ∧
      cnt n E v ≤ ((Hon F).filter fun j => v ∈ A j).card + F.card := by
  constructor
  · apply Finset.card_le_card
    intro j hj
    simp only [Hon, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rw [hEA j hj.1]; exact hj.2
  · unfold cnt
    have : Finset.univ.filter (fun j => v ∈ E j) ⊆ ((Hon F).filter fun j => v ∈ A j) ∪ F := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_union, Hon, Finset.mem_filter, Finset.mem_univ, true_and]
      by_cases hjF : j ∈ F
      · exact Or.inr hjF
      · exact Or.inl ⟨hjF, hEA j hjF ▸ hj⟩
    exact (Finset.card_le_card this).trans (Finset.card_union_le _ _)

lemma mem_atLeast {E : Fin n → Finset ℕ} {k v : ℕ} (hk : 0 < k) :
    v ∈ atLeast n E k ↔ k ≤ cnt n E v := by
  unfold atLeast
  simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, and_iff_right_iff_imp]
  intro h
  obtain ⟨j, hj⟩ := Finset.card_pos.1 (lt_of_lt_of_le hk h)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact ⟨j, hj⟩

/-- The Ready sets received from honest processes. -/
lemma readySets_honest (p : Fin n) : ∀ j ∉ F,
    readySets (t := t) (sel := sel) F x adv p j = (run n t sel F x adv 2 j).rdy := by
  intro j hj; simp [readySets, hj]

variable (hF : F.card ≤ t) (hn : 3 * t < n)
include hF hn

/-- **Lemma 27.** An id timely at a correct process is accepted by every correct process. -/
theorem lemma_27 {p q : Fin n} (hp : p ∉ F) (hq : q ∉ F) {v : ℕ}
    (hv : v ∈ (run n t sel F x adv 3 p).timely) : v ∈ (run n t sel F x adv 3 q).acc := by
  rw [(run_three hp).1, mem_atLeast (by omega)] at hv
  rw [(run_three hq).2, mem_atLeast (by omega)]
  have h1 := (cnt_bounds _ (fun j => (run n t sel F x adv 2 j).rdy) (readySets_honest p) v).2
  have h2 := (cnt_bounds _ (fun j => (run n t sel F x adv 2 j).rdy) (readySets_honest q) v).1
  omega

/-- **Lemma 28.** Every correct id is timely at every correct process. -/
theorem lemma_28 {j₀ q : Fin n} (hj₀ : j₀ ∉ F) (hq : q ∉ F) :
    x j₀ ∈ (run n t sel F x adv 3 q).timely := by
  have hHon : n - t ≤ (Hon F).card := by rw [card_Hon]; omega
  -- every correct process has `x j₀` among its Round-1 ids
  have hids : ∀ j ∉ F, x j₀ ∈ (run n t sel F x adv 1 j).ids := by
    intro j hj
    rw [run_one_ids hj]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨j₀, by simp [hj₀]⟩
  -- hence every correct process sends Ready for it
  have hrdy : ∀ k ∉ F, x j₀ ∈ (run n t sel F x adv 2 k).rdy := by
    intro k hk
    rw [run_two_rdy hk, mem_atLeast (by omega)]
    refine le_trans ?_ (cnt_bounds (F := F) _ (fun j => (run n t sel F x adv 1 j).ids)
      (fun j hj => by simp [hj]) (x j₀)).1
    refine hHon.trans (Finset.card_le_card fun j hj => ?_)
    simp only [Hon, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨hj, hids j hj⟩
  rw [(run_three hq).1, mem_atLeast (by omega)]
  refine le_trans ?_ (cnt_bounds _ (fun j => (run n t sel F x adv 2 j).rdy) (readySets_honest q) (x j₀)).1
  refine hHon.trans (Finset.card_le_card fun j hj => ?_)
  simp only [Hon, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact ⟨hj, hrdy j hj⟩

/-- **Lemma 29.** An id accepted by a correct process was received in Round 1 by at least `n - 2t`
correct processes. -/
theorem lemma_29 {p : Fin n} (hp : p ∉ F) {v : ℕ} (hv : v ∈ (run n t sel F x adv 3 p).acc) :
    n - 2 * t ≤ ((Hon F).filter fun j => v ∈ (run n t sel F x adv 1 j).ids).card := by
  rw [(run_three hp).2, mem_atLeast (by omega)] at hv
  have h1 := (cnt_bounds _ (fun j => (run n t sel F x adv 2 j).rdy) (readySets_honest p) v).2
  -- some correct process sent Ready for `v`
  obtain ⟨k, hk⟩ : ((Hon F).filter fun j => v ∈ (run n t sel F x adv 2 j).rdy).Nonempty := by
    apply Finset.card_pos.1; omega
  simp only [Hon, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  have h2 := hk.2
  rw [run_two_rdy hk.1, mem_atLeast (by omega)] at h2
  have h3 := (cnt_bounds (F := F)
      (fun j => if j ∈ F then echoOf (adv 1 j k) else (run n t sel F x adv 1 j).ids)
      (fun j => (run n t sel F x adv 1 j).ids) (fun j hj => by simp [hj]) v).2
  omega

/-- **Lemma 30** (counting part): the ids accepted by a correct process are among the ids received
in Round 1 by at least `n - 2t` correct processes, and there are at most `n + ⌊t²/(n - 2t)⌋` of
those (if the correct processes have distinct ids). -/
theorem lemma_30 (hinj : Set.InjOn x {j | j ∉ F}) {p : Fin n} (hp : p ∉ F) :
    (run n t sel F x adv 3 p).acc.card ≤ n + t ^ 2 / (n - 2 * t) := by
  classical
  set f := F.card
  set I : Fin n → Finset ℕ := fun j => (run n t sel F x adv 1 j).ids
  -- candidate ids: received by at least `n - 2t` correct processes
  set U : Finset ℕ := ((Hon F).biUnion I).filter fun v =>
    n - 2 * t ≤ ((Hon F).filter fun j => v ∈ I j).card
  set C : Finset ℕ := (Hon F).image x
  have hacc : (run n t sel F x adv 3 p).acc ⊆ U := by
    intro v hv
    have h := lemma_29 hF hn hp hv
    simp only [U, Finset.mem_filter, Finset.mem_biUnion]
    refine ⟨?_, h⟩
    obtain ⟨j, hj⟩ := Finset.card_pos.1 (lt_of_lt_of_le (by omega : 0 < n - 2 * t) h)
    simp only [Finset.mem_filter] at hj
    exact ⟨j, hj.1, hj.2⟩
  have hC : C.card = n - f := by
    rw [Finset.card_image_of_injOn, card_Hon]
    intro a ha b hb hab
    simp only [Hon, Finset.coe_filter, Finset.mem_univ, true_and] at ha hb
    exact hinj ha hb hab
  -- the non-correct ids received by a correct process come from the `f` Byzantine links
  have hIC : ∀ j ∈ Hon F, (I j \ C).card ≤ f := by
    intro j hj
    simp only [Hon, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have : I j \ C ⊆ F.biUnion fun b => identOf (adv 0 b j) := by
      intro v hv
      simp only [I, Finset.mem_sdiff, run_one_ids hj, Finset.mem_biUnion, Finset.mem_univ,
        true_and] at hv
      obtain ⟨⟨b, hb⟩, hvC⟩ := hv
      by_cases hbF : b ∈ F
      · simp only [hbF, if_true] at hb
        exact Finset.mem_biUnion.2 ⟨b, hbF, hb⟩
      · simp only [hbF, if_false, Finset.mem_singleton] at hb
        exact absurd (hb ▸ Finset.mem_image.2 ⟨b, by simp [Hon, hbF], rfl⟩) hvC
    refine (Finset.card_le_card this).trans (Finset.card_biUnion_le.trans ?_)
    calc _ ≤ ∑ _b ∈ F, 1 := Finset.sum_le_sum fun b _ => by
          unfold identOf; split <;> simp
      _ = f := by simp [f]
  -- double counting
  have hdc : (U \ C).card * (n - 2 * t) ≤ (n - f) * f := by
    calc (U \ C).card * (n - 2 * t)
        ≤ ∑ v ∈ U \ C, ((Hon F).filter fun j => v ∈ I j).card := by
          rw [← smul_eq_mul]
          refine Finset.card_nsmul_le_sum _ _ _ fun v hv => ?_
          simp only [Finset.mem_sdiff, U, Finset.mem_filter] at hv
          exact hv.1.2
      _ = ∑ j ∈ Hon F, ((U \ C).filter fun v => v ∈ I j).card := by
          simp only [Finset.card_filter]; exact Finset.sum_comm
      _ ≤ ∑ _j ∈ Hon F, f := Finset.sum_le_sum fun j hj =>
          le_trans (Finset.card_le_card fun v hv => by
            simp only [Finset.mem_filter, Finset.mem_sdiff] at hv ⊢; exact ⟨hv.2, hv.1.2⟩)
            (hIC j hj)
      _ = (n - f) * f := by rw [Finset.sum_const, card_Hon, smul_eq_mul]
  have hUC : U.card ≤ C.card + (U \ C).card := by
    have := Finset.card_sdiff_add_card_inter U C
    have h2 := Finset.card_le_card (Finset.inter_subset_right (s₁ := U) (s₂ := C))
    omega
  -- arithmetic: `(n - f) + ⌊(n - f) f / (n - 2t)⌋ ≤ n + ⌊t² / (n - 2t)⌋`
  have hm : 0 < n - 2 * t := by omega
  have hdiv : (U \ C).card ≤ (n - f) * f / (n - 2 * t) := (Nat.le_div_iff_mul_le hm).2 hdc
  have hkey : (n - f) * f ≤ f * (n - 2 * t) + t ^ 2 := by
    have h1 : f ≤ n := by omega
    have h2 : 2 * t ≤ n := by omega
    zify [h1, h2]
    nlinarith [sq_nonneg ((t : ℤ) - f)]
  have hdiv2 : (n - f) * f / (n - 2 * t) ≤ f + t ^ 2 / (n - 2 * t) := by
    calc (n - f) * f / (n - 2 * t) ≤ (f * (n - 2 * t) + t ^ 2) / (n - 2 * t) :=
          Nat.div_le_div_right hkey
      _ = f + t ^ 2 / (n - 2 * t) := by
          rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.add_comm]
  have := Finset.card_le_card hacc
  omega

omit hF in
/-- For `n > 3t`, Lemma 30 gives at most `n + t - 1` accepted ids (Theorem 39's namespace). -/
lemma lemma_30_namespace (ht : 1 ≤ t) : n + t ^ 2 / (n - 2 * t) ≤ n + t - 1 := by
  have hm : t + 1 ≤ n - 2 * t := by omega
  have h1 : t ^ 2 / (n - 2 * t) ≤ t ^ 2 / (t + 1) := Nat.div_le_div_left hm (by omega)
  have h2 : t ^ 2 / (t + 1) < t := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; nlinarith
  omega

omit hF hn in
/-- **Lemma 40** (counting part): for `n > t² + 2t`, Lemma 30 gives at most `n` accepted ids. -/
lemma lemma_40_count (h : t ^ 2 + 2 * t < n) : n + t ^ 2 / (n - 2 * t) = n := by
  rw [Nat.div_eq_of_lt (by omega)]; rfl

end Podc.OrderPreservingByzRenaming.Alg5
