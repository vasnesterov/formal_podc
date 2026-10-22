import Papers.PODC2016.RationalConsensus.Model

/-!
# Theorem 1: no fair consensus protocol is an `f`-Nash equilibrium

[Halpern, Vilaça, *Rational Consensus*, PODC 2016], Theorem 1: if `σ⃗` solves fair consensus,
agents care only about consensus and `f ≥ 1`, then `σ⃗` is not an `f`-Nash equilibrium.

The proof follows the paper. Fix an agent `i`, the preferences `v` (`i` prefers `1`, everybody
else `0`), and the failure patterns where only `i` crashes. We order them linearly:
`step s` lets `i` crash in round `⌊s/(n-1)⌋ + 1` reaching the first `s mod (n-1)` other agents
(in a fixed enumeration). Consecutive patterns differ by one message from `i` to one agent `j`
(`step_succ_deliv`). In `step 0` agent `i` is silent, so by validity the decision is `0`
(`prob_step_zero`); for large `s` the decision is `1` with positive probability, by fairness in
the failure-free context (`exists_prob_step_ne_zero`). At the first `s` where the probability of
deciding `1` becomes positive, agent `j` gains by pretending not to have received `i`'s message
(`outcome_deviate_step`). This replaces the paper's "minimal failure pattern `F*`" by the first
index in a linear order; it also handles the identification of "crash in round `m + 1` reaching
nobody" with "crash in round `m` reaching everybody", which the paper makes by convention.

The theorem needs `n ≥ 2`; for `n = 1` it is false (`theorem_1_false_of_card_eq_one`).
-/

namespace Podc.RationalConsensus

open Cslib Cslib.SyncCrash MeasureTheory
open scoped ENNReal

variable {P M Ω : Type*} [MeasurableSpace Ω]

/-! ### Expected utility as a finite sum -/

lemma Outcome.univ_eq : (Finset.univ : Finset Outcome) = {.cons true, .cons false, .noCons} := by
  decide

/-- Expected utility over the three outcomes. -/
lemma expUtil_eq_sum [Fintype P] {μ : Measure (P → Ω)} [IsFiniteMeasure μ] {u : Utility P}
    {σ : Profile P M Ω} {c : Context P} {i : P} (hX : AEMeasurable (outcome σ c) μ) :
    expUtil μ u σ c i = ∑ o, μ.real {ω | outcome σ c ω = o} * u.val i (c.pref i) o := by
  unfold expUtil
  rw [← integral_map hX (Measurable.of_discrete.aestronglyMeasurable),
    integral_fintype (Integrable.of_finite)]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [smul_eq_mul, measureReal_def, measureReal_def,
    Measure.map_apply_of_aemeasurable hX (MeasurableSet.of_discrete)]
  rfl

lemma sum_measureReal_outcome [Fintype P] {μ : Measure (P → Ω)} [IsProbabilityMeasure μ]
    {σ : Profile P M Ω} {c : Context P} (hX : AEMeasurable (outcome σ c) μ) :
    ∑ o, μ.real {ω | outcome σ c ω = o} = 1 := by
  have h := sum_measureReal_singleton (μ := μ.map (outcome σ c)) Finset.univ
  rw [Finset.coe_univ, probReal_univ] at h
  rw [← h]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [measureReal_def, measureReal_def,
    Measure.map_apply_of_aemeasurable hX (MeasurableSet.of_discrete)]
  rfl

lemma Utility.val_le_β₀ (u : Utility P) (i : P) (v : Bool) (o : Outcome) :
    u.val i v o ≤ u.β₀ i := by
  have := u.lt₀₁ i; have := u.lt₁₂ i
  cases o with
  | cons b => simp only [Utility.val]; split_ifs <;> linarith
  | noCons => unfold Utility.val; linarith

/-! ### The chain of failure patterns -/

section Chain

variable [Fintype P] [DecidableEq P] (i : P)

/-- Number of agents other than `i`. -/
abbrev kk : ℕ := Fintype.card {a // a ≠ i}

/-- Enumeration of the agents other than `i`. -/
noncomputable abbrev enum : {a // a ≠ i} ≃ Fin (kk i) := Fintype.equivFin _

/-- The set of the first `r` agents other than `i`. -/
def firstAgents (r : ℕ) : Set P := {a | ∃ h : a ≠ i, ((enum i ⟨a, h⟩ : Fin (kk i)) : ℕ) < r}

/-- The `s`-th failure pattern (with preferences `v`): only `i` crashes, in round
`s / (n-1) + 1`, reaching the first `s % (n-1)` other agents. -/
noncomputable def step (v : P → Bool) (s : ℕ) : Context P where
  pref := v
  crash p := if p = i then some (s / kk i + 1) else none
  reach _ := firstAgents i (s % kk i)

variable {i}

lemma step_faulty (v : P → Bool) (s : ℕ) (p : P) : (step i v s).Faulty p ↔ p = i := by
  by_cases h : p = i <;> simp [step, Context.Faulty, h]

lemma step_admissible (v : P → Bool) (s : ℕ) {f : ℕ} (hf : 1 ≤ f) :
    (step i v s).Admissible f := by
  refine ⟨?_, fun p m hm => ?_⟩
  · have : (step i v s).faulty = {i} := by
      ext p; simp [Context.faulty, step_faulty]
    rw [this, Finset.card_singleton]; exact hf
  · simp only [step] at hm
    split_ifs at hm
    obtain rfl := Option.some.inj hm
    exact Nat.succ_pos _

lemma step_deliv_ne (v : P → Bool) (s : ℕ) {Ω : Type*} (ω : P → Ω) {p : P} (hp : p ≠ i) (q : P)
    (t : ℕ) : ((step i v s).run ω).Deliv p q t := by
  simp [Run.Deliv, Run.Alive, step, hp]

lemma step_deliv_self (v : P → Bool) (s : ℕ) {Ω : Type*} (ω : P → Ω) (q : P) (t : ℕ) :
    ((step i v s).run ω).Deliv i q t ↔ t < s / kk i ∨ (t = s / kk i ∧ q ∈ firstAgents i (s % kk i)) := by
  simp only [Run.Deliv, Run.Alive, Context.run_crash, Context.run_reach, step, ite_true,
    Option.some.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    have := h1 _ rfl
    by_cases ht : t = s / kk i
    · exact Or.inr ⟨ht, by by_contra hq; exact h2 ⟨by omega, hq⟩⟩
    · left; omega
  · rintro (h | ⟨h, hq⟩)
    · exact ⟨fun c hc => by omega, fun h' => by omega⟩
    · exact ⟨fun c hc => by omega, fun h' => h'.2 hq⟩

lemma exists_ne_of_two_le (hn : 2 ≤ Fintype.card P) (i : P) : ∃ j, j ≠ i := by
  by_contra h
  push Not at h
  have : Fintype.card P ≤ 1 := Fintype.card_le_one_iff.2 fun a b => (h a).trans (h b).symm
  omega

lemma kk_pos (hn : 2 ≤ Fintype.card P) : 0 < kk i := by
  obtain ⟨j, hj⟩ := exists_ne_of_two_le hn i
  exact Fintype.card_pos_iff.2 ⟨⟨j, hj⟩⟩

/-- The agent that `i` reaches in addition when passing from `step s` to `step (s + 1)`. -/
noncomputable def nextAgent (i : P) (hn : 2 ≤ Fintype.card P) (s : ℕ) : P :=
  ((enum i).symm ⟨s % kk i, Nat.mod_lt _ (kk_pos hn)⟩).1

lemma nextAgent_ne (hn : 2 ≤ Fintype.card P) (s : ℕ) : nextAgent i hn s ≠ i :=
  ((enum i).symm _).2

lemma mem_firstAgents_succ (hn : 2 ≤ Fintype.card P) (s : ℕ) (q : P) :
    q ∈ firstAgents i (s % kk i + 1) ↔ q ∈ firstAgents i (s % kk i) ∨ q = nextAgent i hn s := by
  simp only [firstAgents, Set.mem_ofPred_eq, nextAgent]
  constructor
  · rintro ⟨hq, h⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · exact Or.inl ⟨hq, h⟩
    · right
      have : (enum i).symm ⟨s % kk i, Nat.mod_lt _ (kk_pos hn)⟩ = ⟨q, hq⟩ := by
        rw [Equiv.symm_apply_eq]; ext; exact h.symm
      rw [this]
  · rintro (⟨hq, h⟩ | rfl)
    · exact ⟨hq, by omega⟩
    · exact ⟨nextAgent_ne hn s, by simp⟩

lemma not_step_deliv_next (hn : 2 ≤ Fintype.card P) (v : P → Bool) (s : ℕ) {Ω : Type*}
    (ω : P → Ω) : ¬ ((step i v s).run ω).Deliv i (nextAgent i hn s) (s / kk i) := by
  rw [step_deliv_self]
  rintro (h | ⟨-, hq, h⟩)
  · omega
  · simp [nextAgent] at h

/-- Consecutive failure patterns differ by exactly one message: from `i` to `nextAgent s` in round
`s / (n-1) + 1`. -/
lemma step_succ_deliv (hn : 2 ≤ Fintype.card P) (v : P → Bool) (s : ℕ) {Ω : Type*} (ω : P → Ω)
    (p q : P) (t : ℕ) (hpq : p ≠ q) :
    ((step i v (s + 1)).run ω).Deliv p q t ↔
      ((step i v s).run ω).Deliv p q t ∨ (p = i ∧ q = nextAgent i hn s ∧ t = s / kk i) := by
  by_cases hp : p ≠ i
  · simp [step_deliv_ne v _ ω hp, hp]
  push Not at hp
  subst hp
  have hk := kk_pos (i := p) hn
  have hmod := Nat.mod_lt s hk
  rw [step_deliv_self, step_deliv_self]
  by_cases hlt : s % kk p + 1 < kk p
  · have h1 : (s + 1) / kk p = s / kk p ∧ (s + 1) % kk p = s % kk p + 1 := by
      rw [Nat.div_mod_unique hk]
      exact ⟨by rw [add_comm (s % kk p + 1), ← add_assoc, Nat.div_add_mod], hlt⟩
    rw [h1.1, h1.2, mem_firstAgents_succ hn]
    simp only [true_and]
    constructor
    · rintro (h | ⟨rfl, h | rfl⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨rfl, h⟩)
      · exact Or.inr ⟨rfl, rfl⟩
    · rintro ((h | ⟨rfl, h⟩) | ⟨rfl, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, Or.inl h⟩
      · exact Or.inr ⟨rfl, Or.inr rfl⟩
  · have heq : s % kk p + 1 = kk p := by omega
    have h1 : (s + 1) / kk p = s / kk p + 1 ∧ (s + 1) % kk p = 0 := by
      rw [Nat.div_mod_unique hk]
      refine ⟨?_, hk⟩
      have := Nat.div_add_mod s (kk p)
      rw [mul_add, mul_one]; omega
    rw [h1.1, h1.2]
    have hall : q ∈ firstAgents p (s % kk p) ∨ q = nextAgent p hn s := by
      rw [← mem_firstAgents_succ hn, heq]
      exact ⟨hpq.symm, (enum p ⟨q, hpq.symm⟩).2⟩
    have hnone : q ∉ firstAgents p 0 := by simp [firstAgents]
    constructor
    · rintro (h | ⟨h, h'⟩)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
        · exact Or.inl (Or.inl h)
        · rcases hall with h | h
          · exact Or.inl (Or.inr ⟨rfl, h⟩)
          · exact Or.inr ⟨rfl, h, rfl⟩
      · exact absurd h' hnone
    · rintro ((h | ⟨rfl, -⟩) | ⟨-, -, rfl⟩)
      · left; omega
      · left; omega
      · left; omega

end Chain

/-! ### The proof -/

section Proof

variable [Fintype P] [DecidableEq P] {μ : Measure (P → Ω)} {σ : Profile P M Ω} {f : ℕ} {i : P}

/-- The preferences used in the proof: `i` prefers `1`, everybody else `0`. -/
def prefs (i : P) : P → Bool := fun p => decide (p = i)

omit [MeasurableSpace Ω] [Fintype P] [DecidableEq P] in
/-- In a context where some agent other than `i` is nonfaulty and all agents but possibly `i` prefer
`0`, a consensus run whose outcome is `cons true` must have `i` preferring `1`; in particular if
everybody prefers `0`, a consensus run ends with `cons false`. -/
lemma outcome_false_of_allFalse {c : Context P} {ω : P → Ω} {j : P} (hj : ¬ c.Faulty j)
    (hpref : ∀ p, c.pref p = false) (h : IsConsensusRun σ c ω) :
    outcome σ c ω = .cons false := by
  obtain ⟨b, hb⟩ := h.exists_outcome hj
  have hc := (outcome_eq_cons_iff hj b).1 hb
  obtain ⟨b', hb', q, hq⟩ := h.validity j _ (hc j hj)
  cases hb'
  rw [hpref] at hq
  rw [hb, ← hq]

/-- In `step 0`, agent `i` is silent, so the decision is `0` almost surely. -/
lemma prob_step_zero (hn : 2 ≤ Fintype.card P) (hf : 1 ≤ f) (hσ : SolvesFairConsensus μ σ f) :
    μ {ω | outcome σ (step i (prefs i) 0) ω = .cons true} = 0 := by
  obtain ⟨j, hj⟩ := exists_ne_of_two_le hn i
  set c0 := step i (prefs i) 0
  let c0' : Context P := { c0 with pref := fun _ => false }
  have hadm : c0'.Admissible f := step_admissible (i := i) (fun _ => false) 0 hf
  have hj' : ¬ c0'.Faulty j := by
    rw [show c0'.Faulty j ↔ (step i (fun _ => false) 0).Faulty j from Iff.rfl, step_faulty]
    exact hj
  refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 (hσ.consensus c0' hadm))
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro hcons
  have h1 := outcome_false_of_allFalse hj' (fun _ => rfl) hcons
  have h2 : outcome σ c0 ω = outcome σ c0' ω := by
    refine outcome_eq_of_status (fun p => Iff.rfl) fun p hp => ?_
    have hpi : p ≠ i := by rwa [step_faulty] at hp
    refine status_congr_silent (c := c0) (c' := c0') σ ω (fun q hq => ?_) rfl rfl (fun q t => ?_) p hpi
    · simp [c0', c0, step, prefs, hq]
    · rw [step_deliv_self]
      rintro (h | ⟨-, hq⟩)
      · simp at h
      · simp [firstAgents] at hq
  rw [h2, h1] at hω
  exact absurd hω (by decide)

/-- For some `T`, the decision is `1` with positive probability when `i` crashes in round `T + 2`
reaching nobody (i.e. after the decisions of a failure-free run). -/
lemma exists_prob_step_ne_zero (hn : 2 ≤ Fintype.card P)
    (hσ : SolvesFairConsensus μ σ f) :
    ∃ T, μ {ω | outcome σ (step i (prefs i) ((T + 1) * kk i)) ω = .cons true} ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := exists_ne_of_two_le hn i
  let c1 : Context P := ⟨prefs i, fun _ => none, fun _ => ∅⟩
  have hadm : c1.Admissible f := by
    refine ⟨?_, fun p m hm => by simp [c1] at hm⟩
    have : c1.faulty = ∅ := by ext p; simp [Context.faulty, Context.Faulty, c1]
    simp [this]
  have hnf : ∀ p, ¬ c1.Faulty p := fun p => by simp [Context.Faulty, c1]
  -- fairness: probability at least `1 / n` of deciding `1`
  have hpos : μ {ω | outcome σ c1 ω = .cons true} ≠ 0 := by
    have hfair := hσ.fair c1 hadm true
    have hcard : (Finset.univ.filter fun p => ¬ c1.Faulty p ∧ c1.pref p = true) = {i} := by
      ext p; simp [hnf, c1, prefs]
    rw [hcard, Finset.card_singleton, Nat.cast_one] at hfair
    intro h0
    rw [h0, nonpos_iff_eq_zero, ENNReal.div_eq_zero_iff] at hfair
    simp at hfair
  -- decisions by a fixed time `T`
  let E : ℕ → Set (P → Ω) := fun T => {ω | ∀ p, ∃ t ≤ T,
    status σ c1 ω p t = some (some true) ∧ ∀ t' < t, status σ c1 ω p t' = none}
  have hsub : {ω | outcome σ c1 ω = .cons true} ⊆ ⋃ T, E T := by
    intro ω hω
    have hc := (outcome_eq_cons_iff (hnf i) true).1 hω
    choose r hr hlt using fun p => hc p (hnf p)
    refine Set.mem_iUnion.2 ⟨Finset.univ.sup r, fun p => ⟨r p, ?_, hr p, hlt p⟩⟩
    exact Finset.le_sup (Finset.mem_univ p)
  obtain ⟨T, hT⟩ : ∃ T, μ (E T) ≠ 0 := by
    by_contra h
    push Not at h
    exact hpos (measure_mono_null hsub (measure_iUnion_null_iff.2 h))
  refine ⟨T, fun h0 => hT (measure_mono_null (fun ω hω => ?_) h0)⟩
  set c2 := step i (prefs i) ((T + 1) * kk i)
  have hk := kk_pos (i := i) hn
  have hdiv : (T + 1) * kk i / kk i = T + 1 := Nat.mul_div_cancel _ hk
  -- the runs agree up to time `T + 1`
  have hh : ∀ t ≤ T + 1, ∀ p, hist σ (c1.run ω) t p = hist σ (c2.run ω) t p := by
    refine hist_congr (fun p => rfl) fun t ht p q => ?_
    have : (c1.run ω).Deliv p q t := ⟨fun c hc => by simp [c1] at hc, fun h => by simp [c1] at h⟩
    simp only [this, true_iff]
    by_cases hp : p = i
    · subst hp; rw [step_deliv_self, hdiv]; left; omega
    · exact step_deliv_ne _ _ ω hp q t
  have hst : ∀ p, p ≠ i → ∀ t ≤ T + 1, status σ c2 ω p t = status σ c1 ω p t := by
    intro p hp t ht
    have hal : ((c2.run ω).Alive p t ↔ (c1.run ω).Alive p t) := by
      simp [Run.Alive, c2, c1, step, hp]
    simp only [status, SyncCrash.state]
    by_cases ha : (c1.run ω).Alive p t
    · rw [ite_eq_left (hal.2 ha), ite_eq_left ha, hh t ht p]; rfl
    · rw [ite_eq_right (fun h => ha (hal.1 h)), ite_eq_right ha]
  have hj2 : ¬ c2.Faulty j := by rw [step_faulty]; exact hj
  simp only [Set.mem_ofPred_eq]
  rw [outcome_eq_cons_iff hj2]
  intro p hp
  have hpi : p ≠ i := by rwa [step_faulty] at hp
  obtain ⟨t, ht, h1, h2⟩ := hω p
  refine ⟨t, by rw [hst p hpi t (by omega)]; exact h1, fun t' ht' => ?_⟩
  rw [hst p hpi t' (by omega)]; exact h2 t' ht'

omit [MeasurableSpace Ω] in
/-- **The profitable deviation.** In `step (s + 1)`, if `nextAgent s` ignores the message from `i`
of round `s / (n-1) + 1`, the outcome is the outcome of `σ` in `step s`. -/
lemma outcome_deviate_step (hn : 2 ≤ Fintype.card P) (s : ℕ) (ω : P → Ω) :
    outcome (deviate σ (ignore σ i (s / kk i)) (nextAgent i hn s)) (step i (prefs i) (s + 1)) ω =
      outcome σ (step i (prefs i) s) ω := by
  refine (outcome_eq_of_status (fun p => (step_faulty _ _ p).trans (step_faulty _ _ p).symm)
    fun p hp => ?_).symm
  have hpi : p ≠ i := by rwa [step_faulty] at hp
  refine (status_ignore (c := step i (prefs i) s) (c' := step i (prefs i) (s + 1)) σ
    (nextAgent_ne hn s).symm rfl (fun q hq => ?_)
    (fun p q t hpq => step_succ_deliv hn _ s ω p q t hpq) (not_step_deliv_next hn _ s ω) p
    hpi).symm
  simp [step, hq]

/-- **Theorem 1** of [Halpern–Vilaça]. If `σ⃗` solves fair consensus, agents care only about
consensus (`u : Utility P`) and `f ≥ 1`, then `σ⃗` is not an `f`-Nash equilibrium. (We assume
`n ≥ 2`; see `theorem_1_false_of_card_eq_one` for `n = 1`.) -/
theorem theorem_1 (hn : 2 ≤ Fintype.card P) (μ : Measure (P → Ω)) [IsProbabilityMeasure μ]
    (u : Utility P) (σ : Profile P M Ω) {f : ℕ} (hf : 1 ≤ f)
    (hσ : SolvesFairConsensus μ σ f) : ¬ IsNash μ u σ f := by
  intro hN
  obtain ⟨i⟩ : Nonempty P := Fintype.card_pos_iff.1 (by omega)
  let Pr : ℕ → ℝ≥0∞ := fun s => μ {ω | outcome σ (step i (prefs i) s) ω = .cons true}
  have h0 : Pr 0 = 0 := prob_step_zero hn hf hσ
  have hex : ∃ s, Pr s ≠ 0 := by
    obtain ⟨T, hT⟩ := exists_prob_step_ne_zero (i := i) hn hσ
    exact ⟨_, hT⟩
  classical
  set s₁ := Nat.find hex
  have hs₁ : Pr s₁ ≠ 0 := Nat.find_spec hex
  have hs₁0 : s₁ ≠ 0 := fun h => hs₁ (h ▸ h0)
  obtain ⟨s, hs⟩ : ∃ s, s₁ = s + 1 := ⟨s₁ - 1, by omega⟩
  have hPs : Pr s = 0 := by
    by_contra h
    exact Nat.find_min hex (show s < s₁ by omega) h
  have hPs1 : Pr (s + 1) ≠ 0 := hs ▸ hs₁
  -- the deviation of `j` in `step (s + 1)`
  set j := nextAgent i hn s
  have hji : j ≠ i := nextAgent_ne hn s
  set c := step i (prefs i) (s + 1)
  set c₀ := step i (prefs i) s
  set τ := ignore σ i (s / kk i)
  obtain ⟨hmeas, hnash⟩ := hN c (step_admissible _ _ hf)
  have hmeas₀ := (hN c₀ (step_admissible _ _ hf)).1
  have hdev : outcome (deviate σ τ j) c = outcome σ c₀ := funext (outcome_deviate_step hn s)
  have hle := hnash j τ (hdev ▸ hmeas₀)
  rw [add_zero] at hle
  have hprefj : c.pref j = false := by simp [c, step, prefs, hji]
  have hj : ¬ c.Faulty j := by rw [step_faulty]; exact hji
  have hj₀ : ¬ c₀.Faulty j := by rw [step_faulty]; exact hji
  -- the deviation yields consensus on `0` (`j`'s preference) almost surely
  have hdevU : expUtil μ u (deviate σ τ j) c j = u.β₀ j := by
    unfold expUtil
    rw [hdev, hprefj]
    have hae : ∀ᵐ ω ∂μ, outcome σ c₀ ω = .cons false := by
      filter_upwards [hσ.consensus c₀ (step_admissible _ _ hf),
        measure_eq_zero_iff_ae_notMem.1 hPs] with ω hω hω'
      obtain ⟨b, hb⟩ := hω.exists_outcome hj₀
      cases b
      · exact hb
      · exact absurd hb hω'
    rw [integral_congr_ae (hae.mono fun ω hω => by rw [hω]), integral_const, probReal_univ,
      one_smul]
    simp [Utility.val]
  -- following `σ` yields consensus on `1` with positive probability
  have hσU : expUtil μ u σ c j < u.β₀ j := by
    rw [expUtil_eq_sum hmeas, hprefj]
    have hsum := sum_measureReal_outcome (μ := μ) hmeas
    have hnc : μ.real {ω | outcome σ c ω = .noCons} = 0 := by
      rw [measureReal_eq_zero_iff]
      refine measure_mono_null (fun ω hω => ?_)
        (ae_iff.1 (hσ.consensus c (step_admissible _ _ hf)))
      intro h
      obtain ⟨b, hb⟩ := h.exists_outcome hj
      simp only [Set.mem_ofPred_eq] at hω
      rw [hω] at hb; cases hb
    have hpt : 0 < μ.real {ω | outcome σ c ω = .cons true} := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos hPs1 (measure_ne_top _ _)
    rw [Outcome.univ_eq] at hsum ⊢
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
      at hsum ⊢
    rw [hnc] at hsum ⊢
    simp only [Utility.val, Bool.true_eq_false, ite_false, ite_true, zero_mul, add_zero]
      at hsum ⊢
    have hpf : μ.real {ω | outcome σ c ω = .cons false} =
        1 - μ.real {ω | outcome σ c ω = .cons true} := by linarith
    rw [hpf]
    nlinarith [mul_pos hpt (sub_pos.2 (u.lt₀₁ j))]
  linarith

/-! ### `n = 1`: the theorem fails -/

/-- The one-agent protocol: decide your own preference immediately. -/
def soloProfile (P M Ω : Type*) : Profile P M Ω where
  send _ _ _ _ := none
  decide _ x _ := some (some x.1)

/-- **Theorem 1 needs `n ≥ 2`.** With a single agent, deciding one's own preference at once
solves fair consensus and is an `f`-Nash equilibrium for every `f` (every measure `μ`, every
utility). -/
theorem theorem_1_false_of_card_eq_one [Unique P] (μ : Measure (P → Ω)) [IsProbabilityMeasure μ]
    (u : Utility P) (f : ℕ) :
    SolvesFairConsensus μ (soloProfile P M Ω) f ∧ IsNash μ u (soloProfile P M Ω) f := by
  classical
  set σ := soloProfile P M Ω
  -- decisions of `σ`: the agent decides its preference at time `0` if it is alive then
  have hdec : ∀ (c : Context P) ω (p : P), ¬ c.Faulty p → Decides σ c ω p (some (c.pref p)) := by
    intro c ω p hp
    refine ⟨0, ?_, fun t ht => by omega⟩
    have : (c.run ω).Alive p 0 := Run.alive_of_not_faulty (show ¬ (c.run ω).Faulty p from hp) 0
    simp [status, SyncCrash.state, this, σ, soloProfile]
  have hdec' : ∀ (c : Context P) ω (p : P) o, Decides σ c ω p o → o = some (c.pref p) := by
    rintro c ω p o ⟨t, ht, -⟩
    simp only [status, SyncCrash.state] at ht
    split_ifs at ht
    · simpa [σ, soloProfile] using ht.symm
    · simp at ht
  have hout : ∀ (c : Context P) ω, outcome σ c ω =
      if c.Faulty default then Outcome.noCons else Outcome.cons (c.pref default) := by
    intro c ω
    split_ifs with h
    · -- no nonfaulty agent: both `ConsOn` hold
      have hc : ∀ b, ConsOn σ c ω b := fun b p hp => absurd (Unique.eq_default p ▸ h) hp
      simp [outcome, hc]
    · rw [outcome_eq_cons_iff h]
      intro p hp
      rw [Unique.eq_default p]; exact hdec c ω _ (Unique.eq_default p ▸ hp)
  have hmeas : ∀ c : Context P, AEMeasurable (outcome σ c) μ := fun c => by
    rw [funext (hout c)]; exact aemeasurable_const
  refine ⟨⟨fun c _ => Filter.Eventually.of_forall fun ω => ⟨?_, ?_, ?_⟩, fun c _ b => ?_⟩,
    fun c _ => ⟨hmeas c, fun i τ hτ => ?_⟩⟩
  · intro p q _ _ o o' ho ho'
    rw [hdec' c ω p o ho, hdec' c ω q o' ho', Unique.eq_default p, Unique.eq_default q]
  · exact fun p hp => ⟨_, hdec c ω p hp⟩
  · exact fun p o ho => ⟨_, hdec' c ω p o ho, p, rfl⟩
  · by_cases h : c.Faulty default
    · have : (Finset.univ.filter fun p => ¬ c.Faulty p ∧ c.pref p = b) = ∅ := by
        ext p; simp [Unique.eq_default p, h]
      rw [this]; simp
    · by_cases hb : c.pref default = b
      · have : {ω | outcome σ c ω = .cons b} = Set.univ := by
          ext ω; simp [hout, h, hb]
        rw [this, measure_univ]
        refine ENNReal.div_le_of_le_mul ?_
        rw [one_mul]
        exact_mod_cast Finset.card_le_univ _
      · have : (Finset.univ.filter fun p => ¬ c.Faulty p ∧ c.pref p = b) = ∅ := by
          ext p; simp [Unique.eq_default p, hb]
        rw [this]; simp
  · -- `i` is the only agent; the deviation can do no better than consensus on its preference
    rw [add_zero]
    have hi : i = default := Unique.eq_default i
    by_cases h : c.Faulty default
    · -- nobody is nonfaulty: no consensus, whatever `i` does
      have hc : ∀ (σ' : Profile P M Ω) ω b, ConsOn σ' c ω b :=
        fun _ _ b p hp => absurd (Unique.eq_default p ▸ h) hp
      have h1 : ∀ σ' : Profile P M Ω, outcome σ' c = fun _ => .noCons := fun σ' => by
        funext ω; simp [outcome, hc]
      simp [expUtil, h1]
    · have hσv : expUtil μ u σ c i = u.β₀ i := by
        simp [expUtil, hout, h, hi, Utility.val]
      rw [hσv, expUtil_eq_sum hτ]
      calc ∑ o, μ.real {ω | outcome (deviate σ τ i) c ω = o} * u.val i (c.pref i) o
          ≤ ∑ o, μ.real {ω | outcome (deviate σ τ i) c ω = o} * u.β₀ i :=
            Finset.sum_le_sum fun o _ =>
              mul_le_mul_of_nonneg_left (u.val_le_β₀ i _ o) measureReal_nonneg
        _ = u.β₀ i := by rw [← Finset.sum_mul, sum_measureReal_outcome hτ, one_mul]

end Proof

end Podc.RationalConsensus
