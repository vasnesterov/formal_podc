import Papers.PODC2011.CoordinatedConsensusDynamic.Model

/-!
# Upper bounds for `Δ`-coordinated consensus (Section 6): the approximate `Δ`-ladder and the
clear-majority protocol

* `firstFire R`: the decision rule "decide the value of the first rule `R G u s` (`s ≤ t`) that
  fires". It is local and stable as soon as each `R · u s` is local at time `s`.
* **Lemma 6.3** (`ladder_solves`): the *approximate `Δ`-ladder*. Levels `k = 0, …, kmax`; at time
  `n - kΔ - 1` (for `kΔ + 1 ≤ n`) an undecided node decides `v` if the local formula `Φ k v` holds.
  Since `Φ k v` is local at that time, `K_u Φ = Φ` (`knows_iff_of_local`), so the paper's
  hypotheses are stated for `Φ` directly (`LadderSpec`). The level-`0` rule (time `n - 1`) is
  implicit in the paper (needed for termination and referred to by conditions (a), (b)).
* **Lemma 6.2** (`clearMajority_solves`, `clearMajority_decides`, `clearMajority_decides_eps`):
  the clear-majority protocol, as an instance of the ladder.
-/

namespace CoordCons

open DGraph

/-! ### Locality helpers -/

namespace DGraph.Indist

variable {α : Type*} {G H : DGraph α}

/-- The view determines the causal past (no validity assumption needed). -/
theorem past_eq' {u t : ℕ} (h : Indist G H u t) (s : ℕ) : G.past u t s = H.past u t s := by
  ext v
  simp only [mem_past]
  exact ⟨fun ⟨_, hr⟩ => ⟨(h.reach hr).2.mem_right, h.reach_iff.1 hr⟩,
    fun ⟨_, hr⟩ => ⟨(h.symm.reach hr).2.mem_right, h.reach_iff.2 hr⟩⟩

end DGraph.Indist

/-- Knowledge is a function of the view. -/
theorem knows_congr {α : Type*} {S : DGraph α → Prop} {G H : DGraph α} {u t : ℕ}
    (h : Indist G H u t) {φ : DGraph α → Prop} : Knows S G u t φ ↔ Knows S H u t φ :=
  ⟨fun hk K hK hHK => hk K hK (h.trans hHK), fun hk K hK hGK => hk K hK (h.symm.trans hGK)⟩

/-- For a fact that is local at `(u, t)`, `K_u φ ↔ φ` (in a system containing the actual
execution). This justifies stating the ladder hypotheses for `Φ` instead of `K_u Φ`. -/
theorem knows_iff_of_local {α : Type*} {S : DGraph α → Prop} {G : DGraph α} (hS : S G)
    (hG : G.Valid) {u t : ℕ} (hu : u ∈ G.V) {φ : DGraph α → Prop}
    (hφ : ∀ H, Indist G H u t → (φ G ↔ φ H)) : Knows S G u t φ ↔ φ G :=
  ⟨fun hk => hk G hS (Indist.refl hG hu t), fun h H _ hGH => (hφ H hGH).1 h⟩

/-! ### First-firing decision rules -/

/-- `firstFire R G u t`: the value of the first rule `R G u s`, `s ≤ t`, that fires. -/
def firstFire (R : DGraph Bool → ℕ → ℕ → Option Bool) : Decision Bool
  | G, u, 0 => R G u 0
  | G, u, t + 1 => (firstFire R G u t).or (R G u (t + 1))

section firstFire

variable {R : DGraph Bool → ℕ → ℕ → Option Bool} {G : DGraph Bool} {u : ℕ}

theorem firstFire_succ {t : ℕ} {v : Bool} (h : firstFire R G u t = some v) :
    firstFire R G u (t + 1) = some v := by
  simp [firstFire, h]

theorem firstFire_le {t t' : ℕ} {v : Bool} (h : firstFire R G u t = some v) (htt : t ≤ t') :
    firstFire R G u t' = some v := by
  induction t' with
  | zero => obtain rfl : t = 0 := by omega
            exact h
  | succ t' ih =>
    rcases Nat.eq_or_lt_of_le htt with rfl | hlt
    · exact h
    · exact firstFire_succ (ih (by omega))

theorem exists_of_firstFire {t : ℕ} {v : Bool} (h : firstFire R G u t = some v) :
    ∃ s ≤ t, R G u s = some v := by
  induction t with
  | zero => exact ⟨0, le_rfl, h⟩
  | succ t ih =>
    cases hf : firstFire R G u t with
    | none =>
      simp only [firstFire, hf, Option.none_or] at h
      exact ⟨t + 1, le_rfl, h⟩
    | some w =>
      simp only [firstFire, hf, Option.some_or] at h
      obtain ⟨s, hs, h'⟩ := ih (hf.trans h)
      exact ⟨s, by omega, h'⟩

theorem firstFire_isSome {s t : ℕ} (h : (R G u s).isSome) (hst : s ≤ t) :
    (firstFire R G u t).isSome := by
  have : (firstFire R G u s).isSome := by
    cases s with
    | zero => simpa [firstFire] using h
    | succ s =>
      cases hf : firstFire R G u s with
      | none => simpa [firstFire, hf] using h
      | some w => simp [firstFire, hf]
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 this
  simp [firstFire_le hv hst]

theorem firstFire_local (hR : ∀ G H u s, Indist G H u s → R G u s = R H u s) :
    Local (firstFire R) := by
  intro G H u t h
  induction t with
  | zero => exact hR G H u 0 h
  | succ t ih => simp only [firstFire, ih h.pred, hR G H u (t + 1) h]

end firstFire

/-! ### The approximate `Δ`-ladder (Lemma 6.3) -/

open Classical in
/-- The approximate `Δ`-ladder's rule at time `s`: decide `v` if for some level `k ≤ kmax` with
`s = n - kΔ - 1` the local decision formula `Φ k v` holds (`true` is preferred if both values
qualify, which never happens in admissible executions). Level `0` is the time-`(n-1)` rule. -/
noncomputable def ladderRule (Δ kmax : ℕ) (Φ : ℕ → Bool → DGraph Bool → ℕ → Prop)
    (G : DGraph Bool) (u s : ℕ) : Option Bool :=
  if ∃ k ≤ kmax, s + k * Δ + 1 = G.N ∧ Φ k true G u then some true
  else if ∃ k ≤ kmax, s + k * Δ + 1 = G.N ∧ Φ k false G u then some false
  else none

/-- The approximate `Δ`-ladder protocol (as a decision rule). -/
noncomputable def ladder (Δ kmax : ℕ) (Φ : ℕ → Bool → DGraph Bool → ℕ → Prop) : Decision Bool :=
  firstFire (ladderRule Δ kmax Φ)

/-- Hypotheses of Lemma 6.3. `val G` is the value the underlying eventual-consensus algorithm `A`
decides in `G` (so "`(G, n-1)` is `v`-valent" is `val G = v`); `Φ k v G u` is the level-`k`
decision formula of `u`, evaluated at time `n - kΔ - 1`. -/
structure LadderSpec (S : DGraph Bool → Prop) (Δ kmax : ℕ)
    (Φ : ℕ → Bool → DGraph Bool → ℕ → Prop) (val : DGraph Bool → Bool) : Prop where
  /-- `u` can evaluate `Φ k v` from its local state at time `n - kΔ - 1`. -/
  loc : ∀ k v G H u, Indist G H u (G.N - k * Δ - 1) → (Φ k v G u ↔ Φ k v H u)
  /-- The count is positive and known (`N = n`). -/
  N_pos : ∀ G, S G → 0 < G.N
  /-- Validity of the underlying algorithm `A`. -/
  val_valid : ∀ G, S G → ∃ w ∈ G.V, G.input w = val G
  /-- (a) Consistency: `Φ⁰ᵛ → (A = v)`. -/
  consistency : ∀ G, S G → ∀ u ∈ G.V, ∀ v, Φ 0 v G u → val G = v
  /-- (b) Timeliness: `Φ⁰⁰ ∨ Φ⁰¹` at time `n - 1`. -/
  timeliness : ∀ G, S G → ∀ u ∈ G.V, ∃ v, Φ 0 v G u
  /-- (c) Coordination: `K_u Φᵏᵛ` at `n - kΔ - 1` implies `⋀_w K_w Φᵏ⁻¹ᵛ` at `n - (k-1)Δ - 1`
  (with `K = id` for local formulas). -/
  coordination : ∀ G, S G → ∀ k, 1 ≤ k → k ≤ kmax → k * Δ + 1 ≤ G.N → ∀ u ∈ G.V, ∀ v,
    Φ k v G u → ∀ w ∈ G.V, Φ (k - 1) v G w

section ladder

variable {S : DGraph Bool → Prop} {Δ kmax : ℕ} {Φ : ℕ → Bool → DGraph Bool → ℕ → Prop}
  {val : DGraph Bool → Bool}

theorem ladderRule_eq_some {G : DGraph Bool} {u s : ℕ} {v : Bool}
    (h : ladderRule Δ kmax Φ G u s = some v) :
    ∃ k ≤ kmax, s + k * Δ + 1 = G.N ∧ Φ k v G u := by
  unfold ladderRule at h
  split_ifs at h with h1 h2
  · cases h; exact h1
  · cases h; exact h2

theorem ladderRule_isSome {G : DGraph Bool} {u s : ℕ} {v : Bool}
    (h : ∃ k ≤ kmax, s + k * Δ + 1 = G.N ∧ Φ k v G u) :
    (ladderRule Δ kmax Φ G u s).isSome := by
  unfold ladderRule
  split_ifs with h1 h2
  · rfl
  · rfl
  · exfalso
    cases v
    · exact h2 h
    · exact h1 h

open Classical in
theorem ladderRule_local (hloc : ∀ k v G H u, Indist G H u (G.N - k * Δ - 1) →
    (Φ k v G u ↔ Φ k v H u)) {G H : DGraph Bool} {u s : ℕ} (h : Indist G H u s) :
    ladderRule Δ kmax Φ G u s = ladderRule Δ kmax Φ H u s := by
  have hN := h.N_eq
  have e : ∀ v, (∃ k ≤ kmax, s + k * Δ + 1 = G.N ∧ Φ k v G u) ↔
      (∃ k ≤ kmax, s + k * Δ + 1 = H.N ∧ Φ k v H u) := by
    intro v
    rw [← hN]
    refine exists_congr fun k => and_congr_right fun _ => and_congr_right fun hk => ?_
    exact hloc k v G H u (by rwa [show G.N - k * Δ - 1 = s by omega])
  unfold ladderRule
  exact if_congr (e true) rfl (if_congr (e false) rfl rfl)

/-- In an admissible execution every firing of a level-`k` rule for `v` certifies `A = v`
(iterate (c) down to level `0`, then (a)). In particular two levels can never fire for different
values. -/
theorem LadderSpec.val_eq (hs : LadderSpec S Δ kmax Φ val) {G : DGraph Bool} (hG : S G) :
    ∀ k, k ≤ kmax → k * Δ + 1 ≤ G.N → ∀ u ∈ G.V, ∀ v, Φ k v G u → val G = v := by
  intro k
  induction k with
  | zero => intro _ _ u hu v h; exact hs.consistency G hG u hu v h
  | succ k ih =>
    intro hk hkN u hu v h
    have h' := hs.coordination G hG (k + 1) (by omega) hk hkN u hu v h u hu
    exact ih (by omega) (le_trans (by nlinarith) hkN) u hu v h'

/-- **Lemma 6.3.** Any instantiation of the approximate `Δ`-ladder solves `Δ`-coordinated
consensus. -/
theorem ladder_solves (hs : LadderSpec S Δ kmax Φ val) :
    Consensus S (ladder Δ kmax Φ) ∧ Coordinated S Δ (ladder Δ kmax Φ) := by
  have key : ∀ G, S G → ∀ u ∈ G.V, ∀ t v, ladder Δ kmax Φ G u t = some v → val G = v := by
    intro G hG u hu t v h
    obtain ⟨s, -, hs'⟩ := exists_of_firstFire h
    obtain ⟨k, hk, hkN, hΦ⟩ := ladderRule_eq_some hs'
    exact hs.val_eq hG k hk (by omega) u hu v hΦ
  have term : ∀ G, S G → ∀ u ∈ G.V, (ladderRule Δ kmax Φ G u (G.N - 1)).isSome := by
    intro G hG u hu
    obtain ⟨v, hv⟩ := hs.timeliness G hG u hu
    have := hs.N_pos G hG
    exact ladderRule_isSome ⟨0, Nat.zero_le _, by omega, hv⟩
  refine ⟨⟨firstFire_local (fun G H u s h => ladderRule_local hs.loc h),
    fun G _ u _ t v h => firstFire_succ h, ?_, ?_, ?_⟩, ?_⟩
  · intro G hG u hu w hw t t' a b ha hb
    rw [← key G hG u hu t a ha, ← key G hG w hw t' b hb]
  · intro G hG u hu t v h
    rw [← key G hG u hu t v h]
    exact hs.val_valid G hG
  · intro G hG u hu
    exact ⟨_, firstFire_isSome (term G hG u hu) le_rfl⟩
  · intro G hG u hu t hsome w hw
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsome
    obtain ⟨s, hst, hs'⟩ := exists_of_firstFire hv
    obtain ⟨k, hk, hkN, hΦ⟩ := ladderRule_eq_some hs'
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · exact firstFire_isSome (term G hG w hw) (by omega)
    · have hΦw := hs.coordination G hG k hk1 hk (by omega) u hu v hΦ w hw
      refine firstFire_isSome (s := s + Δ) (ladderRule_isSome ⟨k - 1, by omega, ?_, hΦw⟩)
        (by omega)
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      rw [← hkN]
      ring

/-- A ladder with `Δ ≥ n` never decides before time `n - 1` (all levels `k ≥ 1` are void). -/
theorem ladder_eq_none_of_le {G : DGraph Bool} {u t : ℕ} (hΔ : G.N ≤ Δ) (ht : t + 1 < G.N) :
    ladder Δ kmax Φ G u t = none := by
  cases h : ladder Δ kmax Φ G u t with
  | none => rfl
  | some v =>
    obtain ⟨s, hst, hs'⟩ := exists_of_firstFire h
    obtain ⟨k, -, hkN, -⟩ := ladderRule_eq_some hs'
    rcases Nat.eq_zero_or_pos k with rfl | hk1
    · omega
    · have : Δ ≤ k * Δ := Nat.le_mul_of_pos_left Δ hk1
      omega

end ladder

/-! ### The clear-majority protocol (Lemma 6.2) -/

section clearMajority

open Classical

/-- Number of inputs equal to `b` that `u` has heard of by time `t`. -/
noncomputable def heard (G : DGraph Bool) (u t : ℕ) (b : Bool) : ℕ :=
  ((G.past u t 0).filter (fun w => G.input w = b)).card

/-- Number of inputs equal to `b` in `G`. -/
noncomputable def cnt (G : DGraph Bool) (b : Bool) : ℕ :=
  (G.V.filter (fun w => G.input w = b)).card

/-- The majority value (ties broken in favour of `false`). -/
noncomputable def majority (G : DGraph Bool) : Bool := decide (cnt G false < cnt G true)

/-- Decision formulas of the clear-majority protocol: at level `k ≥ 1` (time `tₖ = n - kΔ - 1`)
"heard at least `⌊n/2⌋ + 1 + C(k,2)Δ` copies of `v`"; at level `0` (time `n - 1`) "the
majority of the inputs heard is `v`". -/
noncomputable def PhiCM (Δ : ℕ) (k : ℕ) (v : Bool) (G : DGraph Bool) (u : ℕ) : Prop :=
  if k = 0 then decide (heard G u (G.N - 1) false < heard G u (G.N - 1) true) = v
  else G.N / 2 + 1 + k.choose 2 * Δ ≤ heard G u (G.N - k * Δ - 1) v

/-- The clear-majority protocol with decision points `tₖ = n - kΔ - 1`, `k = 1, …, kmax`. -/
noncomputable def clearMajority (Δ kmax : ℕ) : Decision Bool := ladder Δ kmax (PhiCM Δ)

variable {G H : DGraph Bool}

theorem heard_congr {u t : ℕ} (h : Indist G H u t) (b : Bool) : heard G u t b = heard H u t b := by
  unfold heard
  rw [← h.past_eq' 0]
  congr 1
  apply Finset.filter_congr
  intro w hw
  rw [h.input_eq (mem_past.1 hw).2]

theorem heard_le_cnt (u t : ℕ) (b : Bool) : heard G u t b ≤ cnt G b :=
  Finset.card_le_card (Finset.filter_subset_filter _ (past_subset _ _ _))

theorem cnt_le_heard_add (u t : ℕ) (b : Bool) :
    cnt G b ≤ heard G u t b + (G.V \ G.past u t 0).card := by
  unfold cnt heard
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro w hw
  rw [Finset.mem_filter] at hw
  by_cases hp : w ∈ G.past u t 0
  · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hp, hw.2⟩)
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hw.1, hp⟩)

theorem cnt_add (G : DGraph Bool) : cnt G true + cnt G false = G.V.card := by
  unfold cnt
  have := Finset.card_filter_add_card_filter_not (s := G.V) (fun w => G.input w = true)
  simpa using this

/-- At time `t`, `u` has heard all but at most `n - (t+1)` copies of `b`. -/
theorem cnt_le_heard (hG : G.Valid) {u : ℕ} (hu : u ∈ G.V) (t : ℕ) (b : Bool) :
    cnt G b ≤ heard G u t b + (G.V.card - (t + 1)) :=
  le_trans (cnt_le_heard_add u t b) (Nat.add_le_add_left (card_sdiff_past_le hG hu) _)

theorem heard_eq_cnt (hG : G.Valid) {u t : ℕ} (hu : u ∈ G.V) (ht : G.V.card ≤ t + 1)
    (b : Bool) : heard G u t b = cnt G b := by
  unfold heard cnt
  rw [past_eq_V hG hu (by omega)]

theorem phiCM_loc (Δ : ℕ) : ∀ k v G H u, Indist G H u (G.N - k * Δ - 1) →
    (PhiCM Δ k v G u ↔ PhiCM Δ k v H u) := by
  intro k v G H u h
  have hN := h.N_eq
  by_cases hk : k = 0
  · subst hk
    rw [show G.N - 0 * Δ - 1 = G.N - 1 by simp] at h
    simp only [PhiCM, ↓reduceIte]
    rw [heard_congr h, heard_congr h, hN]
  · simp only [PhiCM, hk, ↓reduceIte]
    rw [heard_congr h, hN]

/-- The hypotheses of Lemma 6.3 hold for the clear-majority formulas. -/
theorem clearMajority_spec (n Δ kmax : ℕ) :
    LadderSpec (KnownN n) Δ kmax (PhiCM Δ) majority where
  loc := phiCM_loc Δ
  N_pos G hG := by
    rw [hG.2.2, ← hG.2.1]; exact Finset.card_pos.2 hG.1.nonempty
  val_valid G hG := by
    have hpos := Finset.card_pos.2 hG.1.nonempty
    have hc := cnt_add G
    by_cases hm : cnt G false < cnt G true
    · obtain ⟨w, hw⟩ := Finset.card_pos.1 (show 0 < cnt G true by omega)
      rw [Finset.mem_filter] at hw
      exact ⟨w, hw.1, by simp [majority, hm, hw.2]⟩
    · obtain ⟨w, hw⟩ := Finset.card_pos.1 (show 0 < cnt G false by omega)
      rw [Finset.mem_filter] at hw
      exact ⟨w, hw.1, by simp [majority, hm, hw.2]⟩
  consistency G hG u hu v h := by
    have h1 := hG.2.1
    have h2 := hG.2.2
    simp only [PhiCM, ↓reduceIte] at h
    rw [heard_eq_cnt hG.1 hu (by omega), heard_eq_cnt hG.1 hu (by omega)] at h
    exact h
  timeliness G hG u hu :=
    ⟨decide (heard G u (G.N - 1) false < heard G u (G.N - 1) true), by simp [PhiCM]⟩
  coordination G hG k hk1 hk hkN u hu v h w hw := by
    obtain ⟨hV, hcard, hN⟩ := hG
    simp only [PhiCM, show k ≠ 0 by omega, ↓reduceIte] at h
    rw [hN] at hkN h
    have hcu := le_trans h (heard_le_cnt (G := G) u _ v)
    have hc := cnt_add G
    rcases Nat.eq_or_lt_of_le hk1 with rfl | hk2
    · simp only [PhiCM, Nat.sub_self, ↓reduceIte, hN]
      rw [heard_eq_cnt hV hw (by omega), heard_eq_cnt hV hw (by omega)]
      cases v <;> simp <;> omega
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      simp only [PhiCM, show j + 2 - 1 = j + 1 by omega, Nat.add_one_ne_zero, ↓reduceIte, hN]
      have hw' := cnt_le_heard hV hw (n - (j + 1) * Δ - 1) v
      have hch : (j + 2).choose 2 = (j + 1).choose 2 + (j + 1) := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
      rw [hch] at hcu
      have e2 : (j + 2) * Δ = (j + 1) * Δ + Δ := by ring
      rw [e2] at hkN
      have e3 : ((j + 1).choose 2 + (j + 1)) * Δ = (j + 1).choose 2 * Δ + (j + 1) * Δ := by ring
      rw [e3] at hcu
      omega

/-- **Lemma 6.2 (first part).** The clear-majority protocol solves `Δ`-coordinated consensus
when the count `n` is known, for every `n`, `Δ` and `kmax`. -/
theorem clearMajority_solves (n Δ kmax : ℕ) :
    Consensus (KnownN n) (clearMajority Δ kmax) ∧
      Coordinated (KnownN n) Δ (clearMajority Δ kmax) :=
  ladder_solves (clearMajority_spec n Δ kmax)

/-- All decisions of the clear-majority protocol are the majority value. -/
theorem clearMajority_eq_majority {n Δ kmax : ℕ} (hG : KnownN n G) {u t : ℕ} (hu : u ∈ G.V)
    {v : Bool} (h : clearMajority Δ kmax G u t = some v) : v = majority G := by
  obtain ⟨s, -, hs'⟩ := exists_of_firstFire h
  obtain ⟨k, hk, hkN, hΦ⟩ := ladderRule_eq_some hs'
  exact ((clearMajority_spec n Δ kmax).val_eq hG k hk (by omega) u hu v hΦ).symm

/-- **Lemma 6.2 (speed, exact form).** If some value `v` has at least
`⌊n/2⌋ + 1 + C(k+1, 2)·Δ = ⌊n/2⌋ + 1 + k(k+1)/2·Δ` copies, `1 ≤ k ≤ kmax` and `kΔ < n`, then
every node has decided by `tₖ = n - kΔ - 1`. -/
theorem clearMajority_decides {n Δ kmax k : ℕ} (hG : KnownN n G) (hk1 : 1 ≤ k) (hk : k ≤ kmax)
    (hkn : k * Δ + 1 ≤ n) {v : Bool} (hv : n / 2 + 1 + (k + 1).choose 2 * Δ ≤ cnt G v) :
    ∀ u ∈ G.V, (clearMajority Δ kmax G u (n - k * Δ - 1)).isSome := by
  intro u hu
  refine firstFire_isSome (ladderRule_isSome (v := v) ⟨k, hk, by rw [hG.2.2]; omega, ?_⟩) le_rfl
  simp only [PhiCM, show k ≠ 0 by omega, ↓reduceIte, hG.2.2]
  have hu' := cnt_le_heard hG.1 hu (n - k * Δ - 1) v
  rw [hG.2.1] at hu'
  have hch : (k + 1).choose 2 = k.choose 2 + k := by
    rw [Nat.choose_succ_succ, Nat.choose_one_right]; ring
  rw [hch, add_mul] at hv
  omega

end clearMajority

/-! ### The `(1/2 + ε)n` form of Lemma 6.2 -/

/-- The paper's choice `kmax = ⌊√((2εn - 1)/Δ) - 1⌋`. -/
noncomputable def kEps (ε : ℝ) (n Δ : ℕ) : ℕ := ⌊√((2 * ε * n - 1) / Δ) - 1⌋₊

/-- **Lemma 6.2 (speed, `ε` form).** If at least `(1/2 + ε)n` inputs equal `v`, `Δ ≥ 1` and
`Δ ≤ (2εn - 1)/4` (the condition used in the paper's proof; the lemma's statement assumes the
stronger `Δ ≤ (εn - 1)/2`), then with `k = ⌊√((2εn - 1)/Δ) - 1⌋ ≤ kmax` every node has decided
by time `n - kΔ - 1`, where `1 ≤ k`, `kΔ < n` and `√((2εn-1)Δ)/4 ≤ kΔ ≤ √((2εn-1)Δ)`;
i.e. after `n - Θ(√(nΔ))` rounds for constant `ε`. -/
theorem clearMajority_decides_eps {n Δ kmax : ℕ} {G : DGraph Bool} (hG : KnownN n G) {ε : ℝ}
    (hΔ : 1 ≤ Δ) (hΔε : 4 * (Δ : ℝ) ≤ 2 * ε * n - 1) {v : Bool}
    (hv : (1 / 2 + ε) * n ≤ cnt G v) (hk : kEps ε n Δ ≤ kmax) :
    1 ≤ kEps ε n Δ ∧ kEps ε n Δ * Δ + 1 ≤ n ∧
      √((2 * ε * n - 1) * Δ) / 4 ≤ (kEps ε n Δ * Δ : ℕ) ∧
      ((kEps ε n Δ * Δ : ℕ) : ℝ) ≤ √((2 * ε * n - 1) * Δ) ∧
      ∀ u ∈ G.V, (clearMajority Δ kmax G u (n - kEps ε n Δ * Δ - 1)).isSome := by
  set a : ℝ := 2 * ε * n - 1 with ha
  set x : ℝ := √(a / Δ) with hx
  set k := kEps ε n Δ with hkdef
  have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hΔpos : (0 : ℝ) < Δ := by linarith
  have ha4 : 4 ≤ a / Δ := by rw [le_div_iff₀ hΔpos]; linarith
  have hx2 : 2 ≤ x := by
    rw [hx, Real.le_sqrt (by norm_num) (by linarith)]; linarith
  have hxsq : x ^ 2 = a / Δ := Real.sq_sqrt (by linarith)
  have hk_le : (k : ℝ) ≤ x - 1 := Nat.floor_le (by linarith)
  have hk_gt : x - 1 < k + 1 := Nat.lt_floor_add_one _
  have hk1 : 1 ≤ k := Nat.le_floor (by push_cast; linarith)
  have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  -- `xΔ = √(aΔ)`
  have hxΔ : x * Δ = √(a * Δ) := by
    rw [hx, show a * Δ = (a / Δ) * (Δ * Δ) by field_simp, Real.sqrt_mul (by linarith),
      Real.sqrt_mul_self hΔpos.le]
  -- `(k+1)²Δ ≤ a`
  have hk2 : ((k : ℝ) + 1) ^ 2 * Δ ≤ a := by
    have : ((k : ℝ) + 1) ^ 2 ≤ a / Δ := by
      rw [← hxsq]; exact pow_le_pow_left₀ (by positivity) (by linarith) 2
    rwa [le_div_iff₀ hΔpos] at this
  -- `ε ≤ 1/2`, hence `a ≤ n - 1`
  have hn : (1 : ℝ) ≤ n := by
    have := Finset.card_pos.2 hG.1.nonempty
    rw [hG.2.1] at this
    exact_mod_cast this
  have hcn : (cnt G v : ℝ) ≤ n := by
    have : cnt G v ≤ n := hG.2.1 ▸ Finset.card_filter_le _ _
    exact_mod_cast this
  have han : a ≤ n - 1 := by nlinarith
  -- `xΔ ≤ a`
  have hxa : x * Δ ≤ a := by
    rw [hxΔ]
    refine Real.sqrt_le_iff.2 ⟨by linarith, ?_⟩
    nlinarith
  refine ⟨hk1, ?_, ?_, ?_, ?_⟩
  · have : (k : ℝ) * Δ + 1 ≤ n := by nlinarith
    exact_mod_cast this
  · rw [← hxΔ]
    push_cast
    have : x / 4 ≤ k := by
      by_cases h4 : x ≤ 4
      · linarith
      · linarith
    nlinarith
  · rw [← hxΔ]; push_cast; nlinarith
  · refine clearMajority_decides hG hk1 hk ?_ (v := v) ?_
    · have : (k : ℝ) * Δ + 1 ≤ n := by nlinarith
      exact_mod_cast this
    · have hc : (((k + 1).choose 2 : ℕ) : ℝ) = (k + 1) * k / 2 := by
        rw [Nat.cast_choose_two]; push_cast; ring
      have hdiv : ((n / 2 : ℕ) : ℝ) ≤ n / 2 := Nat.cast_div_le
      have : ((n / 2 + 1 + (k + 1).choose 2 * Δ : ℕ) : ℝ) ≤ cnt G v := by
        push_cast
        rw [hc]
        nlinarith
      exact_mod_cast this

end CoordCons
