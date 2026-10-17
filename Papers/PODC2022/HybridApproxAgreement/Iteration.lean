import Papers.PODC2022.HybridApproxAgreement.Trim
import Podc.Foundations.Data.Finset.Quorum

/-!
# The analysis of `Π_AA` relative to the Overlap All-to-All Broadcast guarantees (Section 3.1)

`Π_AA` runs `S` iterations; in each iteration every honest party distributes its current value with
an Overlap All-to-All Broadcast (`Π_oBC`), obtains a set `O` of value–sender pairs, forms the
multiset `V` of the values, sets `k := |V| - (n - tₛ)`, discards the `max(tₐ, k)` lowest and highest
values and takes the midpoint of the remaining range.

We model the output of `Π_oBC` at party `p` as a partial map `O p : P → Option ℝ` (the value
attributed to each sender, if any; by `tₛ`- and `tₐ`-Consistency with `P = P'`, a party never holds two
values for the same sender, so this loses nothing), and state the guarantees of Definition 2.2
that the analysis uses:

* `SyncOBC tₛ F x O` (synchronous network): `|F| ≤ tₛ`, `tₛ`-Synchronized Overlap (every honest
  party holds the current value of every honest sender) and `tₛ`-Consistency.
* `AsyncOBC tₛ tₐ F x O` (asynchronous network): `|F| ≤ tₐ`, `tₐ`-Consistency, `(tₛ, tₐ)`-Overlap
  (`|O_P ∩ O_P'| ≥ n - tₛ`) and **authenticity** (a value attributed to an honest sender is its current
  value). Authenticity is *not* part of Definition 2.2, but the proof of Lemma 3.4 uses it ("at most
  `tₐ` values are sent by corrupted parties"); it holds for the paper's `Π_oBC` (by validity and
  consistency of `Π_rBC`).

Main results: `step_sync`/`step_async` (one iteration: Lemmas 3.2–3.5, values stay in the current
honest range and the range is halved), `iterate` (`S` iterations), and `theorem_3_1_sync`,
`theorem_3_1_async`: `Π_AA` is a secure AA protocol in both networks **provided** every invocation of
`Π_oBC` meets the guarantees above. Termination is inherited from `Π_oBC`'s termination.
Whether the paper's `Π_oBC` actually meets them is the subject of `RBC.lean` (it does not in the
synchronous case).
-/

open Multiset

namespace HybridApproxAgreement

set_option linter.unusedSectionVars false

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The senders for which `p` obtained a value. -/
def dom (O : P → Option ℝ) : Finset P := Finset.univ.filter fun q => (O q).isSome

/-- The multiset `V` of the values obtained (line 4 of `Π_AA`). -/
noncomputable def recvVals (O : P → Option ℝ) : Multiset ℝ :=
  (dom O).val.map fun q => (O q).getD 0

/-- The new value of a party (lines 4–7 of `Π_AA`), `n = |P|`. -/
noncomputable def aaStep (ts ta : ℕ) (O : P → Option ℝ) : ℝ :=
  midTrim (recvVals O) (max ta (card (recvVals O) - (Fintype.card P - ts)))

/-- Synchronous guarantees of `Π_oBC` for one invocation (honest parties `∉ F`, honest inputs `x`). -/
structure SyncOBC (ts : ℕ) (F : Finset P) (x : P → ℝ) (O : P → P → Option ℝ) : Prop where
  card_faulty : F.card ≤ ts
  overlap : ∀ p ∉ F, ∀ q ∉ F, O p q = some (x q)
  consistency : ∀ p ∉ F, ∀ p' ∉ F, ∀ q a b, O p q = some a → O p' q = some b → a = b

/-- Asynchronous guarantees of `Π_oBC` for one invocation. -/
structure AsyncOBC (ts ta : ℕ) (F : Finset P) (x : P → ℝ) (O : P → P → Option ℝ) : Prop where
  card_faulty : F.card ≤ ta
  consistency : ∀ p ∉ F, ∀ p' ∉ F, ∀ q a b, O p q = some a → O p' q = some b → a = b
  overlap : ∀ p ∉ F, ∀ p' ∉ F,
    Fintype.card P - ts ≤ (Finset.univ.filter fun q => (O p q).isSome ∧ O p q = O p' q).card
  authentic : ∀ p ∉ F, ∀ q ∉ F, ∀ a, O p q = some a → a = x q

/-! ### Multiset bookkeeping -/

section Bookkeeping

variable {O O' : P → Option ℝ}

theorem card_recvVals : card (recvVals O) = (dom O).card := by simp [recvVals]

theorem card_recvVals_le : card (recvVals O) ≤ Fintype.card P := by
  rw [card_recvVals]; exact Finset.card_le_univ _

/-- `V` restricted to a set of senders. -/
theorem map_le_recvVals {X : Finset P} (hX : X ⊆ dom O) (g : P → ℝ)
    (hg : ∀ q ∈ X, g q = (O q).getD 0) : X.val.map g ≤ recvVals O := by
  unfold recvVals
  rw [show X.val.map g = X.val.map (fun q => (O q).getD 0) from map_congr rfl hg]
  exact map_le_map (Finset.val_le_iff.mpr hX)

/-- With consistency, `|V ∪ V'| ≤ n`. -/
theorem card_union_le (hc : ∀ q a b, O q = some a → O' q = some b → a = b) :
    card (recvVals O ∪ recvVals O') ≤ Fintype.card P := by
  set g : P → ℝ := fun q => if (O q).isSome then (O q).getD 0 else (O' q).getD 0
  have h1 : recvVals O ≤ (dom O ∪ dom O').val.map g := by
    unfold recvVals
    rw [show (dom O).val.map (fun q => (O q).getD 0) = (dom O).val.map g from
      map_congr rfl fun q hq => by simp [dom] at hq; simp [g, hq]]
    exact map_le_map (Finset.val_le_iff.mpr Finset.subset_union_left)
  have h2 : recvVals O' ≤ (dom O ∪ dom O').val.map g := by
    unfold recvVals
    rw [show (dom O').val.map (fun q => (O' q).getD 0) = (dom O').val.map g from
      map_congr rfl fun q hq => by
        simp [dom] at hq
        obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hq
        by_cases h : (O q).isSome
        · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp h
          simp [g, ha, hb, hc q a b ha hb]
        · simp [g, h]]
    exact map_le_map (Finset.val_le_iff.mpr Finset.subset_union_right)
  calc card (recvVals O ∪ recvVals O') ≤ card ((dom O ∪ dom O').val.map g) :=
        card_le_card (union_le h1 h2)
    _ = (dom O ∪ dom O').card := by rw [card_map]; rfl
    _ ≤ Fintype.card P := Finset.card_le_univ _

/-- `|V ∩ V'|` is at least the number of senders with the same value at both parties. -/
theorem card_common_le_inter :
    (Finset.univ.filter fun q => (O q).isSome ∧ O q = O' q).card ≤
      card (recvVals O ∩ recvVals O') := by
  set X := Finset.univ.filter fun q => (O q).isSome ∧ O q = O' q
  have hX : X ⊆ dom O := fun q hq => by simp [X, dom] at hq ⊢; exact hq.1
  have hX' : X ⊆ dom O' := fun q hq => by
    simp [X, dom] at hq ⊢; rw [← hq.2]; exact hq.1
  have h := le_inter (map_le_recvVals hX (fun q => (O q).getD 0) fun _ _ => rfl)
    (map_le_recvVals hX' (fun q => (O q).getD 0) fun q hq => by simp [X] at hq; rw [hq.2])
  simpa using card_le_card h

/-- Splitting `V` into values from senders outside and inside `F`. -/
theorem recvVals_split (F : Finset P) :
    recvVals O = ((dom O).filter (· ∉ F)).val.map (fun q => (O q).getD 0) +
      ((dom O).filter (· ∈ F)).val.map (fun q => (O q).getD 0) := by
  have e : (dom O).val.filter (· ∉ F) + (dom O).val.filter (· ∈ F) = (dom O).val := by
    rw [show (dom O).val.filter (· ∈ F) = (dom O).val.filter (fun q => ¬ q ∉ F) from
      filter_congr fun q _ => by simp]
    exact filter_add_not _ _
  unfold recvVals
  rw [Finset.filter_val, Finset.filter_val, ← map_add, e]

end Bookkeeping

/-! ### One iteration -/

/-- The core of Lemmas 3.2–3.5, on multisets. -/
theorem step_core {n ts ta : ℕ} (hta : ta ≤ ts) (hn : 2 * ts + ta < n) {V V' H C H' C' : Multiset ℝ}
    {lo hi : ℝ} (hV : V = H + C) (hV' : V' = H' + C')
    (hH : ∀ y ∈ H, lo ≤ y ∧ y ≤ hi) (hH' : ∀ y ∈ H', lo ≤ y ∧ y ≤ hi)
    (hC : card C ≤ max ta (card V - (n - ts))) (hC' : card C' ≤ max ta (card V' - (n - ts)))
    (hc1 : n - ts ≤ card V) (hc2 : card V ≤ n) (hc1' : n - ts ≤ card V') (hc2' : card V' ≤ n)
    (hU : card (V ∪ V') ≤ n) (hI : n - ts ≤ card (V ∩ V')) :
    (lo ≤ midTrim V (max ta (card V - (n - ts))) ∧ midTrim V (max ta (card V - (n - ts))) ≤ hi) ∧
      |midTrim V (max ta (card V - (n - ts))) - midTrim V' (max ta (card V' - (n - ts)))| ≤
        (hi - lo) / 2 := by
  have eV : card V = n - ts + (card V - (n - ts)) := by omega
  have eV' : card V' = n - ts + (card V' - (n - ts)) := by omega
  have hk : card V - (n - ts) ≤ ts := by omega
  have hk' : card V' - (n - ts) ≤ ts := by omega
  have h2d := two_mul_max_lt hta hn eV hk
  have h2d' := two_mul_max_lt hta hn eV' hk'
  have hT : ∀ W H C : Multiset ℝ, W = H + C → (∀ y ∈ H, lo ≤ y ∧ y ≤ hi) →
      ∀ d, card C ≤ d → 2 * d < card W → ∀ y ∈ trim W d, lo ≤ y ∧ y ≤ hi := by
    rintro W H C rfl hH d hC hd y hy
    have hv := trim_validity hH hC hd
    have hb := trim_bounds hd hy
    exact ⟨hv.1.trans hb.1, hb.2.trans hv.2⟩
  have T1 := hT V H C hV hH _ hC h2d
  have T2 := hT V' H' C' hV' hH' _ hC' h2d'
  exact ⟨midTrim_mem h2d T1, lemma_3_6 hta hn eV eV' hk hk' hU hI T1 T2⟩

variable {ts ta : ℕ} {F : Finset P} {x : P → ℝ} {O : P → P → Option ℝ}

/-- **Lemmas 3.2 and 3.3** (one iteration, synchronous network). -/
theorem step_sync (hta : ta ≤ ts) (hn : 2 * ts + ta < Fintype.card P) (hO : SyncOBC ts F x O)
    {lo hi : ℝ} (hx : ∀ q ∉ F, lo ≤ x q ∧ x q ≤ hi) :
    (∀ p ∉ F, lo ≤ aaStep ts ta (O p) ∧ aaStep ts ta (O p) ≤ hi) ∧
      ∀ p ∉ F, ∀ p' ∉ F, |aaStep ts ta (O p) - aaStep ts ta (O p')| ≤ (hi - lo) / 2 := by
  have hFc := hO.card_faulty
  -- honest senders are in every honest party's domain
  have hdom : ∀ p ∉ F, (Finset.univ.filter (· ∉ F)) ⊆ (dom (O p)).filter (· ∉ F) := by
    intro p hp q hq
    simp at hq; simp [dom, hO.overlap p hp q hq, hq]
  have hdomeq : ∀ p ∉ F, (dom (O p)).filter (· ∉ F) = Finset.univ.filter (· ∉ F) := fun p hp =>
    Finset.Subset.antisymm (Finset.monotone_filter_left _ (Finset.subset_univ _)) (hdom p hp)
  have hcard : ∀ p ∉ F, Fintype.card P - ts ≤ card (recvVals (O p)) := by
    intro p hp
    rw [card_recvVals]
    have := Finset.card_le_card (Finset.filter_subset (· ∉ F) (dom (O p)))
    rw [hdomeq p hp, Finset.card_filter_notMem_univ] at this
    omega
  have hparts : ∀ p ∉ F, ∃ H C : Multiset ℝ, recvVals (O p) = H + C ∧
      (∀ y ∈ H, lo ≤ y ∧ y ≤ hi) ∧
      card C ≤ max ta (card (recvVals (O p)) - (Fintype.card P - ts)) := by
    intro p hp
    refine ⟨_, _, recvVals_split F, ?_, ?_⟩
    · intro y hy
      simp only [mem_map, Finset.mem_val, Finset.mem_filter] at hy
      obtain ⟨q, ⟨-, hq⟩, rfl⟩ := hy
      rw [hO.overlap p hp q hq]; exact hx q hq
    · have e := congrArg card (recvVals_split (O := O p) F)
      simp only [card_add, card_map, Finset.card_val] at e
      rw [hdomeq p hp, Finset.card_filter_notMem_univ] at e
      have := le_max_right ta (card (recvVals (O p)) - (Fintype.card P - ts))
      simp only [card_map, Finset.card_val]
      omega
  refine ⟨fun p hp => ?_, fun p hp p' hp' => ?_⟩
  · obtain ⟨H, C, e, hH, hC⟩ := hparts p hp
    exact (step_core hta hn e e hH hH hC hC (hcard p hp) card_recvVals_le (hcard p hp)
      card_recvVals_le (by rw [← Multiset.sup_eq_union, sup_idem]; exact card_recvVals_le)
      (by rw [← Multiset.inf_eq_inter, inf_idem]; exact hcard p hp)).1
  · obtain ⟨H, C, e, hH, hC⟩ := hparts p hp
    obtain ⟨H', C', e', hH', hC'⟩ := hparts p' hp'
    refine (step_core hta hn e e' hH hH' hC hC' (hcard p hp) card_recvVals_le (hcard p' hp')
      card_recvVals_le (card_union_le (hO.consistency p hp p' hp')) ?_).2
    refine le_trans ?_ card_common_le_inter
    calc Fintype.card P - ts ≤ (Finset.univ.filter (· ∉ F)).card := by rw [Finset.card_filter_notMem_univ]; omega
      _ ≤ _ := Finset.card_le_card fun q hq => by
          simp at hq; simp [hO.overlap p hp q hq, hO.overlap p' hp' q hq]

/-- **Lemmas 3.4 and 3.5** (one iteration, asynchronous network). -/
theorem step_async (hta : ta ≤ ts) (hn : 2 * ts + ta < Fintype.card P)
    (hO : AsyncOBC ts ta F x O) {lo hi : ℝ} (hx : ∀ q ∉ F, lo ≤ x q ∧ x q ≤ hi) :
    (∀ p ∉ F, lo ≤ aaStep ts ta (O p) ∧ aaStep ts ta (O p) ≤ hi) ∧
      ∀ p ∉ F, ∀ p' ∉ F, |aaStep ts ta (O p) - aaStep ts ta (O p')| ≤ (hi - lo) / 2 := by
  have hFc := hO.card_faulty
  have hcard : ∀ p ∉ F, Fintype.card P - ts ≤ card (recvVals (O p)) := by
    intro p hp
    rw [card_recvVals]
    refine (hO.overlap p hp p hp).trans (Finset.card_le_card fun q hq => ?_)
    simp [dom] at hq ⊢; exact hq
  have hparts : ∀ p ∉ F, ∃ H C : Multiset ℝ, recvVals (O p) = H + C ∧
      (∀ y ∈ H, lo ≤ y ∧ y ≤ hi) ∧
      card C ≤ max ta (card (recvVals (O p)) - (Fintype.card P - ts)) := by
    intro p hp
    refine ⟨_, _, recvVals_split F, ?_, ?_⟩
    · intro y hy
      simp only [mem_map, Finset.mem_val, Finset.mem_filter] at hy
      obtain ⟨q, ⟨hqd, hq⟩, rfl⟩ := hy
      simp [dom] at hqd
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hqd
      rw [ha, Option.getD_some, hO.authentic p hp q hq a ha]; exact hx q hq
    · simp only [card_map, Finset.card_val]
      have := Finset.card_le_card (Finset.filter_subset (· ∈ F) (dom (O p)))
      have h2 : ((dom (O p)).filter (· ∈ F)).card ≤ F.card :=
        Finset.card_le_card fun q hq => by simp at hq; exact hq.2
      have := le_max_left ta (card (recvVals (O p)) - (Fintype.card P - ts))
      omega
  refine ⟨fun p hp => ?_, fun p hp p' hp' => ?_⟩
  · obtain ⟨H, C, e, hH, hC⟩ := hparts p hp
    exact (step_core hta hn e e hH hH hC hC (hcard p hp) card_recvVals_le (hcard p hp)
      card_recvVals_le (by rw [← Multiset.sup_eq_union, sup_idem]; exact card_recvVals_le)
      (by rw [← Multiset.inf_eq_inter, inf_idem]; exact hcard p hp)).1
  · obtain ⟨H, C, e, hH, hC⟩ := hparts p hp
    obtain ⟨H', C', e', hH', hC'⟩ := hparts p' hp'
    exact (step_core hta hn e e' hH hH' hC hC' (hcard p hp) card_recvVals_le (hcard p' hp')
      card_recvVals_le (card_union_le (hO.consistency p hp p' hp'))
      ((hO.overlap p hp p' hp').trans card_common_le_inter)).2

/-! ### Iterations -/

/-- Iterating a step that keeps the honest values in the current range and halves it: after `i`
iterations, the honest values lie in the initial range `[lo, hi]` and are within `(hi - lo) / 2^i`
of each other. -/
theorem iterate {F : Finset P} (hne : ∃ p, p ∉ F) (x : ℕ → P → ℝ)
    (hstep : ∀ i lo hi, (∀ q ∉ F, lo ≤ x i q ∧ x i q ≤ hi) →
      (∀ p ∉ F, lo ≤ x (i + 1) p ∧ x (i + 1) p ≤ hi) ∧
        ∀ p ∉ F, ∀ p' ∉ F, |x (i + 1) p - x (i + 1) p'| ≤ (hi - lo) / 2)
    {lo hi : ℝ} (h0 : ∀ q ∉ F, lo ≤ x 0 q ∧ x 0 q ≤ hi) :
    ∀ i, (∀ p ∉ F, lo ≤ x i p ∧ x i p ≤ hi) ∧
      ∀ p ∉ F, ∀ p' ∉ F, |x i p - x i p'| ≤ (hi - lo) / 2 ^ i := by
  -- invariant: the honest values lie in a subinterval of length `≤ (hi - lo) / 2^i`
  have inv : ∀ i, ∃ a b, lo ≤ a ∧ b ≤ hi ∧ b - a ≤ (hi - lo) / 2 ^ i ∧
      ∀ q ∉ F, a ≤ x i q ∧ x i q ≤ b := by
    intro i
    induction i with
    | zero => exact ⟨lo, hi, le_rfl, le_rfl, by simp, h0⟩
    | succ i ih =>
      obtain ⟨a, b, ha, hb, hab, hq⟩ := ih
      obtain ⟨h1, h2⟩ := hstep i a b hq
      set Hs := Finset.univ.filter (· ∉ F)
      have hHs : Hs.Nonempty := by obtain ⟨p, hp⟩ := hne; exact ⟨p, by simp [Hs, hp]⟩
      obtain ⟨pm, hpm, hmin⟩ := Hs.exists_min_image (x (i + 1)) hHs
      obtain ⟨pM, hpM, hmax⟩ := Hs.exists_max_image (x (i + 1)) hHs
      simp only [Hs, Finset.mem_filter, Finset.mem_univ, true_and] at hpm hpM hmin hmax
      refine ⟨x (i + 1) pm, x (i + 1) pM, ha.trans (h1 pm hpm).1, (h1 pM hpM).2.trans hb, ?_,
        fun q hq => ⟨hmin q hq, hmax q hq⟩⟩
      have := (abs_le.mp (h2 pM hpM pm hpm)).2
      rw [pow_succ]
      calc x (i + 1) pM - x (i + 1) pm ≤ (b - a) / 2 := this
        _ ≤ (hi - lo) / 2 ^ i / 2 := by linarith
        _ = (hi - lo) / (2 ^ i * 2) := by rw [div_div]
  intro i
  obtain ⟨a, b, ha, hb, hab, hq⟩ := inv i
  refine ⟨fun p hp => ⟨ha.trans (hq p hp).1, (hq p hp).2.trans hb⟩, fun p hp p' hp' => ?_⟩
  rw [abs_le]
  constructor <;> linarith [hq p hp, hq p' hp']

/-- `S = ⌈log₂(δmax / ε)⌉` iterations suffice: `δmax ≤ 2^S ε`. -/
theorem le_two_pow_ceil_logb {δmax ε : ℝ} (hδ : 0 ≤ δmax) (hε : 0 < ε) :
    δmax ≤ 2 ^ ⌈Real.logb 2 (δmax / ε)⌉₊ * ε := by
  rw [← div_le_iff₀ hε]
  rcases (div_nonneg hδ hε.le).lt_or_eq with h | h
  · calc δmax / ε = (2 : ℝ) ^ Real.logb 2 (δmax / ε) := (Real.rpow_logb (by norm_num)
          (by norm_num) h).symm
      _ ≤ (2 : ℝ) ^ (⌈Real.logb 2 (δmax / ε)⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
      _ = 2 ^ ⌈Real.logb 2 (δmax / ε)⌉₊ := Real.rpow_natCast _ _
  · rw [← h]; positivity

/-- Honest outputs after `S` iterations, from the bounds of `iterate`: validity w.r.t. the range
`[lo, hi]` of the honest inputs and `ε`-agreement as soon as `hi - lo ≤ δmax ≤ 2^S ε`. -/
theorem agreement_of_iterate {F : Finset P} {x : ℕ → P → ℝ} {lo hi δmax ε : ℝ} {S : ℕ}
    (h : ∀ p ∉ F, ∀ p' ∉ F, |x S p - x S p'| ≤ (hi - lo) / 2 ^ S) (hlen : hi - lo ≤ δmax)
    (hS : δmax ≤ 2 ^ S * ε) : ∀ p ∉ F, ∀ p' ∉ F, |x S p - x S p'| ≤ ε := by
  intro p hp p' hp'
  refine (h p hp p' hp').trans ?_
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- **Theorem 3.1 (1), relative to `Π_oBC`.** In a synchronous network with at most `tₛ`
corruptions, if every invocation of `Π_oBC` satisfies its synchronous guarantees, the honest values
`x i` of `Π_AA` (with `x (i+1) p` computed by lines 4–7 from the `i`-th oBC output) stay in the range
`[lo, hi]` of the honest inputs and after `S` iterations are `ε`-close whenever
`hi - lo ≤ δmax ≤ 2^S ε` (e.g. `S = ⌈log₂(δmax / ε)⌉`, `le_two_pow_ceil_logb`). -/
theorem theorem_3_1_sync (hta : ta ≤ ts) (hn : 2 * ts + ta < Fintype.card P)
    {x : ℕ → P → ℝ} {O : ℕ → P → P → Option ℝ} (hO : ∀ i, SyncOBC ts F (x i) (O i))
    (hx : ∀ i, ∀ p ∉ F, x (i + 1) p = aaStep ts ta (O i p))
    {lo hi δmax ε : ℝ} {S : ℕ} (h0 : ∀ q ∉ F, lo ≤ x 0 q ∧ x 0 q ≤ hi) (hlen : hi - lo ≤ δmax)
    (hS : δmax ≤ 2 ^ S * ε) :
    (∀ p ∉ F, lo ≤ x S p ∧ x S p ≤ hi) ∧ ∀ p ∉ F, ∀ p' ∉ F, |x S p - x S p'| ≤ ε := by
  have hne : ∃ p, p ∉ F := by
    by_contra h; push Not at h
    have : F = Finset.univ := Finset.eq_univ_of_forall h
    have := (hO 0).card_faulty; rw [‹F = _›, Finset.card_univ] at this; omega
  have it := iterate hne x (fun i lo hi hq => by
    have := step_sync hta hn (hO i) hq
    exact ⟨fun p hp => hx i p hp ▸ this.1 p hp,
      fun p hp p' hp' => by rw [hx i p hp, hx i p' hp']; exact this.2 p hp p' hp'⟩) h0 S
  exact ⟨it.1, agreement_of_iterate it.2 hlen hS⟩

/-- **Theorem 3.1 (2), relative to `Π_oBC`.** The same in an asynchronous network with at most `tₐ`
corruptions, if every invocation of `Π_oBC` satisfies its asynchronous guarantees. -/
theorem theorem_3_1_async (hta : ta ≤ ts) (hn : 2 * ts + ta < Fintype.card P)
    {x : ℕ → P → ℝ} {O : ℕ → P → P → Option ℝ} (hO : ∀ i, AsyncOBC ts ta F (x i) (O i))
    (hx : ∀ i, ∀ p ∉ F, x (i + 1) p = aaStep ts ta (O i p))
    {lo hi δmax ε : ℝ} {S : ℕ} (h0 : ∀ q ∉ F, lo ≤ x 0 q ∧ x 0 q ≤ hi) (hlen : hi - lo ≤ δmax)
    (hS : δmax ≤ 2 ^ S * ε) :
    (∀ p ∉ F, lo ≤ x S p ∧ x S p ≤ hi) ∧ ∀ p ∉ F, ∀ p' ∉ F, |x S p - x S p'| ≤ ε := by
  have hne : ∃ p, p ∉ F := by
    by_contra h; push Not at h
    have : F = Finset.univ := Finset.eq_univ_of_forall h
    have := (hO 0).card_faulty; rw [‹F = _›, Finset.card_univ] at this; omega
  have it := iterate hne x (fun i lo hi hq => by
    have := step_async hta hn (hO i) hq
    exact ⟨fun p hp => hx i p hp ▸ this.1 p hp,
      fun p hp p' hp' => by rw [hx i p hp, hx i p' hp']; exact this.2 p hp p' hp'⟩) h0 S
  exact ⟨it.1, agreement_of_iterate it.2 hlen hS⟩

end HybridApproxAgreement
