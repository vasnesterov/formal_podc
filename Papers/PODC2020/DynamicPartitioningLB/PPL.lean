import Papers.PODC2020.DynamicPartitioningLB.Model

/-!
# Theorem 2.2: the Perfect Partition Learner `PPL` is `O(k ℓ)`-competitive

Pacut, Parham, Schmid, PODC 2020, Section 2.2. The paper states Theorem 2.2 without proof; we
prove it with ratio `2 (n - 1)`, `n = k ℓ`, in the static learning model (`IsStaticLearningInput`:
a fixed communication pattern admitting a perfect partition, every communicating pair
communicating forever).

**Algorithm** (`ppl`). PPL maintains components (as a labelling `comp : V → V`, two nodes being in
the same component iff they have the same label) and a configuration collocating every component.
On an inter-cluster request `(u, v)` it merges the components of `u` and `v` and moves to a
balanced component-respecting configuration *closest to the initial configuration* (`closest`).

**Proof.**
* PPL never pays for a request: after a merge it serves the request locally.
* If `P*` is any perfect partition at distance `D` from `init`, `P*` respects every component, so
  PPL's configurations are always at distance `≤ D` from `init`; a repartition costs
  `≤ α (D + D)`. Every repartition merges two components, so there are at most `n - 1` of them:
  `PPL ≤ 2 (n - 1) α D` (`ppl_cost_le`).
* Any offline schedule with bounded cost eventually stays in one configuration, which must be a
  perfect partition (otherwise it pays forever for a pair that communicates forever); reaching it
  costs `α · dist init P* ≥ α D` (`schedule_lb`).
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2020.DynamicPartitioningLB

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {ℓ : ℕ}

/-! ### Costs of prefixes of infinite inputs -/

lemma schedCost_prefixOf (α : ℕ) (σ : ℕ → Req V) (O : ℕ → Config V ℓ) (T : ℕ) :
    schedCost α (prefixOf σ T) O =
      ∑ t ∈ range T, (α * dist (O t) (O (t + 1)) + sep (O (t + 1)) (σ t)) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    rw [prefixOf_succ, schedCost, schedCostFrom_append, ← schedCost, ih, sum_range_succ]
    simp [prefixOf]

lemma dist_le_sum (O : ℕ → Config V ℓ) (T : ℕ) :
    dist (O 0) (O T) ≤ ∑ t ∈ range T, dist (O t) (O (t + 1)) := by
  induction T with
  | zero => simp [dist_self]
  | succ T ih =>
    rw [sum_range_succ]; exact (dist_triangle _ (O T) _).trans (by omega)

/-- If `p` holds infinitely often, it holds at least `m` times before some time `T'`. -/
lemma many_of_frequently {p : ℕ → Prop} [DecidablePred p] (T₀ : ℕ)
    (hp : ∀ T, ∃ t, T ≤ t ∧ p t) :
    ∀ m, ∃ T', m ≤ ((Ico T₀ T').filter p).card := by
  intro m
  induction m with
  | zero => exact ⟨T₀, by simp⟩
  | succ m ih =>
    obtain ⟨T', hT'⟩ := ih
    obtain ⟨t, ht, hpt⟩ := hp (max T₀ T')
    refine ⟨t + 1, ?_⟩
    have hsub : insert t ((Ico T₀ T').filter p) ⊆ (Ico T₀ (t + 1)).filter p := by
      intro x hx
      simp only [mem_insert, mem_filter, mem_Ico] at hx ⊢
      rcases hx with rfl | ⟨⟨h1, h2⟩, h3⟩
      · exact ⟨⟨le_of_max_le_left ht, by omega⟩, hpt⟩
      · exact ⟨⟨h1, by omega⟩, h3⟩
    have hnot : t ∉ (Ico T₀ T').filter p := by
      simp only [mem_filter, mem_Ico, not_and]; intro _ h; exact absurd ht (by omega)
    have := card_le_card hsub
    rw [card_insert_of_notMem hnot] at this
    omega

/-- **Lower bound on any offline schedule** in the static learning model: some prefix costs at
least `α · dist init Q` for some perfect partition `Q`. -/
theorem schedule_lb {k α : ℕ} (hα : 1 ≤ α) {init : Config V ℓ} {σ : ℕ → Req V}
    (hσ : IsStaticLearningInput ℓ k σ) {O : ℕ → Config V ℓ} (hO : IsSchedule k init O) :
    ∃ (T' : ℕ) (Q : Config V ℓ), Balanced k Q ∧ (∀ t, Q (σ t).1 = Q (σ t).2) ∧
      α * dist init Q ≤ schedCost α (prefixOf σ T') O := by
  classical
  obtain ⟨⟨P, hPb, hPσ⟩, hinf⟩ := hσ
  -- bound by the number of "paid" times
  have hcount : ∀ (p : ℕ → Prop) [DecidablePred p] (T₀ T' : ℕ),
      (∀ t, T₀ ≤ t → p t → 1 ≤ α * dist (O t) (O (t + 1)) + sep (O (t + 1)) (σ t)) →
      ((Ico T₀ T').filter p).card ≤ schedCost α (prefixOf σ T') O := by
    intro p _ T₀ T' hp
    rw [schedCost_prefixOf]
    calc ((Ico T₀ T').filter p).card = ∑ t ∈ (Ico T₀ T').filter p, 1 := by simp
      _ ≤ ∑ t ∈ (Ico T₀ T').filter p,
          (α * dist (O t) (O (t + 1)) + sep (O (t + 1)) (σ t)) :=
        sum_le_sum fun t ht => hp t (mem_Ico.1 (mem_filter.1 ht).1).1 (mem_filter.1 ht).2
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (fun t ht => by
          simp only [mem_filter, mem_Ico, mem_range] at ht ⊢; omega) (fun _ _ _ => Nat.zero_le _)
  by_cases hconst : ∃ t₀, ∀ t, t₀ ≤ t → O (t + 1) = O t
  · obtain ⟨t₀, ht₀⟩ := hconst
    have hQ : ∀ t, t₀ ≤ t → O t = O t₀ := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => rfl
      | succ t ht ih => rw [ht₀ t ht, ih]
    by_cases hperf : ∀ t, O t₀ (σ t).1 = O t₀ (σ t).2
    · refine ⟨t₀, O t₀, hO.2 t₀, hperf, ?_⟩
      rw [schedCost_prefixOf, ← hO.1]
      calc α * dist (O 0) (O t₀) ≤ α * ∑ t ∈ range t₀, dist (O t) (O (t + 1)) :=
            Nat.mul_le_mul_left _ (dist_le_sum O t₀)
        _ = ∑ t ∈ range t₀, α * dist (O t) (O (t + 1)) := by rw [mul_sum]
        _ ≤ _ := sum_le_sum fun t _ => Nat.le_add_right _ _
    · push Not at hperf
      obtain ⟨t₁, ht₁⟩ := hperf
      obtain ⟨T', hT'⟩ := many_of_frequently (p := fun t => σ t = σ t₁) t₀
        (fun T => (hinf t₁ T).imp fun _ h => h) (α * dist init P)
      refine ⟨T', P, hPb, hPσ, hT'.trans (hcount _ t₀ T' fun t htt ht => ?_)⟩
      have : sep (O (t + 1)) (σ t) = 1 := by
        rw [ht, hQ (t + 1) (by omega)]; simp [sep, ht₁]
      omega
  · push Not at hconst
    obtain ⟨T', hT'⟩ := many_of_frequently (p := fun t => O (t + 1) ≠ O t) 0
      (fun T => (hconst T).imp fun _ h => h) (α * dist init P)
    refine ⟨T', P, hPb, hPσ, hT'.trans (hcount _ 0 T' fun t _ ht => ?_)⟩
    have : 1 ≤ dist (O t) (O (t + 1)) := by
      obtain ⟨v, hv⟩ := Function.ne_iff.1 ht
      exact one_le_dist_of_ne (Ne.symm hv)
    nlinarith

/-! ### The algorithm -/

/-- `Q` is balanced and collocates every component of the labelling `comp`. -/
def RespC (k : ℕ) (comp : V → V) (Q : Config V ℓ) : Prop :=
  Balanced k Q ∧ ∀ u v, comp u = comp v → Q u = Q v

lemma exists_closest (init : Config V ℓ) {p : Config V ℓ → Prop} (h : ∃ Q, p Q) :
    ∃ Q, p Q ∧ ∀ Q', p Q' → dist init Q ≤ dist init Q' := by
  classical
  have hd : ∃ d, ∃ Q, p Q ∧ dist init Q = d := let ⟨Q, hQ⟩ := h; ⟨_, Q, hQ, rfl⟩
  obtain ⟨Q, hQ, hQd⟩ := Nat.find_spec hd
  exact ⟨Q, hQ, fun Q' hQ' => hQd ▸ Nat.find_min' hd ⟨Q', hQ', rfl⟩⟩

/-- A balanced component-respecting configuration closest to `init` (`P` if there is none). -/
noncomputable def closest (k : ℕ) (init : Config V ℓ) (comp : V → V) (P : Config V ℓ) :
    Config V ℓ :=
  open Classical in
  if h : ∃ Q : Config V ℓ, RespC k comp Q then (exists_closest init h).choose else P

lemma closest_spec {k : ℕ} {init : Config V ℓ} {comp : V → V} (P : Config V ℓ)
    (h : ∃ Q : Config V ℓ, RespC k comp Q) :
    RespC k comp (closest k init comp P) ∧
      ∀ Q, RespC k comp Q → dist init (closest k init comp P) ≤ dist init Q := by
  unfold closest; rw [dite_eq_left h]; exact (exists_closest init h).choose_spec

/-- Merge the components of `a` and `b` (relabel `b`'s component with `a`'s label). -/
def mergeC (comp : V → V) (a b : V) : V → V :=
  fun w => if comp w = comp b then comp a else comp w

/-- State of PPL: the component labelling and the current configuration. -/
structure PState (V : Type*) (ℓ : ℕ) where
  /-- Component labels. -/
  comp : V → V
  /-- Current configuration. -/
  P : Config V ℓ

/-- One step of PPL: on an inter-cluster request, merge and move to the closest
component-respecting configuration. -/
noncomputable def pplStep (k : ℕ) (init : Config V ℓ) (st : PState V ℓ) (r : Req V) :
    PState V ℓ :=
  if st.P r.1 = st.P r.2 then st
  else ⟨mergeC st.comp r.1 r.2, closest k init (mergeC st.comp r.1 r.2) st.P⟩

/-- State of PPL after the requests `σ`. -/
noncomputable def pplState (k : ℕ) (init : Config V ℓ) (σ : List (Req V)) : PState V ℓ :=
  σ.foldl (pplStep k init) ⟨id, init⟩

lemma pplState_append (k : ℕ) (init : Config V ℓ) (σ : List (Req V)) (r : Req V) :
    pplState k init (σ ++ [r]) = pplStep k init (pplState k init σ) r := by
  simp [pplState, List.foldl_append]

lemma pplState_balanced {k : ℕ} {init : Config V ℓ} (hinit : Balanced k init) :
    ∀ σ, Balanced k (pplState k init σ).P := by
  intro σ
  induction σ using List.reverseRecOn with
  | nil => exact hinit
  | append_singleton σ r ih =>
    rw [pplState_append]
    unfold pplStep
    split_ifs
    · exact ih
    · by_cases h : ∃ Q : Config V ℓ, RespC k (mergeC (pplState k init σ).comp r.1 r.2) Q
      · exact (closest_spec _ h).1.1
      · show Balanced k (closest _ _ _ _); unfold closest; rw [dite_eq_right h]; exact ih

/-- The algorithm PPL (Perfect Partition Learner) of Section 2.2. -/
noncomputable def ppl (k : ℕ) (init : Config V ℓ) (hinit : Balanced k init) :
    OnlineAlg V ℓ k init where
  conf σ := (pplState k init σ).P
  conf_nil := rfl
  balanced := pplState_balanced hinit

lemma mergeC_image_card {comp : V → V} {a b : V} (h : comp a ≠ comp b) :
    (univ.image (mergeC comp a b)).card + 1 = (univ.image comp).card := by
  have : univ.image (mergeC comp a b) = (univ.image comp).erase (comp b) := by
    ext c
    simp only [mem_image, mem_univ, true_and, mem_erase, mergeC]
    constructor
    · rintro ⟨w, rfl⟩
      split_ifs with hw
      · exact ⟨h, a, rfl⟩
      · exact ⟨hw, w, rfl⟩
    · rintro ⟨hc, w, rfl⟩
      exact ⟨w, ite_eq_right hc⟩
  rw [this, card_erase_of_mem (mem_image_of_mem _ (mem_univ _))]
  have : 0 < (univ.image comp).card := card_pos.2 ⟨comp b, mem_image_of_mem _ (mem_univ _)⟩
  omega

lemma mergeC_resp {comp : V → V} {a b : V} {Q : Config V ℓ}
    (hQ : ∀ u v, comp u = comp v → Q u = Q v) (hab : Q a = Q b) :
    ∀ u v, mergeC comp a b u = mergeC comp a b v → Q u = Q v := by
  intro u v huv
  unfold mergeC at huv
  split_ifs at huv with h1 h2 h2
  · exact hQ u v (h1.trans h2.symm)
  · exact (hQ u b h1).trans (hab.symm.trans (hQ a v huv))
  · exact (hQ u a huv).trans (hab.trans (hQ b v h2.symm))
  · exact hQ u v huv

lemma mergeC_self (comp : V → V) (a b : V) : mergeC comp a b a = mergeC comp a b b := by
  simp only [mergeC]; split_ifs <;> rfl

/-- **Invariant of PPL.** For any perfect partition `Pst` (balanced, collocating all requests so
far), `Pst` respects the components, PPL's configuration respects the components and is closest
to `init`, and `ALG + 2αD · #components ≤ 2αD · n` with `D = dist init Pst`. -/
theorem ppl_inv {k α : ℕ} {init : Config V ℓ} (hinit : Balanced k init) {Pst : Config V ℓ}
    (hPb : Balanced k Pst) :
    ∀ τ : List (Req V), (∀ r ∈ τ, Pst r.1 = Pst r.2) →
      (∀ u v, (pplState k init τ).comp u = (pplState k init τ).comp v → Pst u = Pst v) ∧
      (∀ u v, (pplState k init τ).comp u = (pplState k init τ).comp v →
        (pplState k init τ).P u = (pplState k init τ).P v) ∧
      (∀ Q, RespC k (pplState k init τ).comp Q →
        dist init (pplState k init τ).P ≤ dist init Q) ∧
      algCost α (ppl k init hinit) τ +
          2 * α * dist init Pst * (univ.image (pplState k init τ).comp).card ≤
        2 * α * dist init Pst * Fintype.card V := by
  intro τ
  induction τ using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨fun u v h => by simp_all [pplState], fun u v h => by simp_all [pplState],
      fun Q _ => by simp [pplState, dist_self], ?_⟩
    simp only [algCost_nil, zero_add, pplState, List.foldl_nil]
    rw [image_id, card_univ]
  | append_singleton τ r ih =>
    intro hτ
    obtain ⟨h1, h2, h3, h4⟩ := ih fun r' hr' => hτ r' (by simp [hr'])
    have hr : Pst r.1 = Pst r.2 := hτ r (by simp)
    set st := pplState k init τ with hst
    have hconf : ∀ σ, (ppl k init hinit).conf σ = (pplState k init σ).P := fun _ => rfl
    rw [algCost_append, hconf, hconf, pplState_append, ← hst]
    unfold pplStep
    split_ifs with hsep
    · refine ⟨h1, h2, h3, ?_⟩
      simp only [dist_self, mul_zero, sep, hsep, ite_true, add_zero]
      exact h4
    · have hne : st.comp r.1 ≠ st.comp r.2 := fun h => hsep (h2 _ _ h)
      have hPst : RespC k (mergeC st.comp r.1 r.2) Pst := ⟨hPb, mergeC_resp h1 hr⟩
      obtain ⟨⟨hP'b, hP'r⟩, hP'min⟩ := closest_spec (init := init) st.P ⟨Pst, hPst⟩
      set P' := closest k init (mergeC st.comp r.1 r.2) st.P
      refine ⟨mergeC_resp h1 hr, hP'r, hP'min, ?_⟩
      simp only
      have hsep' : sep P' r = 0 := sep_eq_zero (hP'r _ _ (mergeC_self _ _ _))
      have hd1 : dist st.P init ≤ dist init Pst := by
        rw [dist_comm]; exact h3 Pst ⟨hPb, h1⟩
      have hd2 : dist init P' ≤ dist init Pst := hP'min Pst hPst
      have hd : α * dist st.P P' ≤ 2 * α * dist init Pst := by
        have := dist_triangle st.P init P'
        calc α * dist st.P P' ≤ α * (dist init Pst + dist init Pst) :=
              Nat.mul_le_mul_left _ (by omega)
          _ = 2 * α * dist init Pst := by ring
      have hcard := mergeC_image_card hne
      have e : 2 * α * dist init Pst * (univ.image st.comp).card =
          2 * α * dist init Pst * (univ.image (mergeC st.comp r.1 r.2)).card +
            2 * α * dist init Pst := by
        rw [← hcard]; ring
      omega

/-- PPL's cost on every prefix is at most `2 (n - 1) α · dist init P*` for every perfect
partition `P*`. -/
theorem ppl_cost_le {k α : ℕ} {init : Config V ℓ} (hinit : Balanced k init) {Pst : Config V ℓ}
    (hPb : Balanced k Pst) {τ : List (Req V)} (hτ : ∀ r ∈ τ, Pst r.1 = Pst r.2) :
    algCost α (ppl k init hinit) τ ≤ 2 * (Fintype.card V - 1) * (α * dist init Pst) := by
  have h := (ppl_inv (α := α) hinit hPb τ hτ).2.2.2
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | h0
  · rw [h0] at h; simp at h; simp [h]
  · have : 1 ≤ (univ.image (pplState k init τ).comp).card := by
      obtain ⟨v⟩ := Fintype.card_pos_iff.1 h0
      exact card_pos.2 ⟨_, mem_image_of_mem _ (mem_univ v)⟩
    have e1 : 2 * (Fintype.card V - 1) * (α * dist init Pst) + 2 * α * dist init Pst =
        2 * α * dist init Pst * Fintype.card V := by
      obtain ⟨m, hm⟩ : ∃ m, Fintype.card V = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
      rw [hm, Nat.add_sub_cancel]; ring
    have e2 : 2 * α * dist init Pst ≤
        2 * α * dist init Pst * (univ.image (pplState k init τ).comp).card :=
      Nat.le_mul_of_pos_right _ this
    omega

/-- **Theorem 2.2** (Pacut, Parham, Schmid, PODC 2020). PPL is `2 (n - 1)`-competitive (strictly,
without additive constant) in the static learning model: for every input `σ` with a static
communication pattern admitting a perfect partition and every admissible offline schedule `O`,
PPL's cost on any prefix is at most `2 (n - 1)` times the cost of `O` on some prefix. With
`n = k ℓ` this is `O(k ℓ)` (`theorem_2_2_kl`). -/
theorem theorem_2_2 {k α : ℕ} (hα : 1 ≤ α) {init : Config V ℓ} (hinit : Balanced k init)
    {σ : ℕ → Req V} (hσ : IsStaticLearningInput ℓ k σ) {O : ℕ → Config V ℓ}
    (hO : IsSchedule k init O) (T : ℕ) :
    ∃ T', algCost α (ppl k init hinit) (prefixOf σ T) ≤
      2 * (Fintype.card V - 1) * schedCost α (prefixOf σ T') O := by
  obtain ⟨T', Q, hQb, hQσ, hcost⟩ := schedule_lb hα hσ hO
  refine ⟨T', (ppl_cost_le hinit hQb fun r hr => ?_).trans (Nat.mul_le_mul_left _ hcost)⟩
  obtain ⟨t, rfl⟩ := mem_prefixOf hr
  exact hQσ t

/-- Theorem 2.2 with `n = k ℓ`: competitive ratio `2 (k ℓ - 1) = O(k ℓ)`. -/
theorem theorem_2_2_kl {k α : ℕ} (hV : Fintype.card V = k * ℓ) (hα : 1 ≤ α)
    {init : Config V ℓ} (hinit : Balanced k init) {σ : ℕ → Req V}
    (hσ : IsStaticLearningInput ℓ k σ) {O : ℕ → Config V ℓ} (hO : IsSchedule k init O)
    (T : ℕ) :
    ∃ T', algCost α (ppl k init hinit) (prefixOf σ T) ≤
      2 * (k * ℓ - 1) * schedCost α (prefixOf σ T') O := by
  rw [← hV]; exact theorem_2_2 hα hinit hσ hO T

end Papers.PODC2020.DynamicPartitioningLB
