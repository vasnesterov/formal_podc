import Papers.PODC2016.RationalConsensus.Model

/-!
# Crash records of `σ_cons` in failure-only runs (combinatorial core of Theorem 2)

In `σ_cons` every agent keeps, for every other agent `l`, the earliest round in which it knows
that `l` crashed ("status reports" `SR[l]`, lines 23–37 of Algorithm 1): it records round
`t + 1` if it receives no round-`t + 1` message from `l`, and it takes the minimum with the
records reported by the agents it hears from. In runs where nobody deviates, the presence of
messages is determined by the failure pattern, so these records are the function `ghost` of the
context below (the protocol is shown to compute exactly `ghost` in `Theorem2.lean`).

From the records at the end of round `f + 1`, an agent computes
`NC R m = {l | m < R l}` (the agents it believes alive after round `m`), the first round
`m ∈ [1, f + 1]` that *seems clean* (`NC m = NC (m - 1)`), and decides using `NC m`.

Main result: `ghost_agree`: all nonfaulty agents compute the same first seemingly clean round
and the same set `NC`. The paper's proof claims that the first round `m*` without crash seems
clean to everybody; this is false (`not_clean_example`), so we prove agreement differently: a
disagreement about an agent `l` at threshold `m` forces `l` to crash in round `m` and a chain of
crashes in each of the rounds `m + 1, …, f + 1` (`crash_chain_of_disagree`); together with the
`m - 1` agents witnessing that rounds `1, …, m - 1` do not seem clean, that is `f + 1` crashes.
-/

namespace Podc.RationalConsensus

open Classical

variable {P : Type*}

/-- Message delivery of a context (independent of the seeds): `p`'s round-`t + 1` message
reaches `q`. -/
def Context.Deliv (c : Context P) (p q : P) (t : ℕ) : Prop :=
  (∀ m, c.crash p = some m → t < m) ∧ ¬ (c.crash p = some (t + 1) ∧ q ∉ c.reach p)

lemma Context.run_deliv {Ω : Type*} (c : Context P) (ω : P → Ω) (p q : P) (t : ℕ) :
    (c.run ω).Deliv p q t ↔ c.Deliv p q t := Iff.rfl

variable [Fintype P]

/-- `ghost c t q l`: the round in which `q`, after `t` rounds, first knows `l` to have crashed
(`⊤`: not known). -/
noncomputable def ghost (c : Context P) : ℕ → P → P → ℕ∞
  | 0, _, _ => ⊤
  | t + 1, q, l =>
    if l = q then ⊤ else
      min (ghost c t q l)
        (min (if c.Deliv l q t then ⊤ else ((t + 1 : ℕ) : ℕ∞))
          (Finset.univ.inf fun y => if y ≠ q ∧ c.Deliv y q t then ghost c t y l else ⊤))

/-- The agents believed not to have crashed up to round `m`, given the records `R`. -/
noncomputable def NC (R : P → ℕ∞) (m : ℕ) : Finset P :=
  Finset.univ.filter fun l => ((m : ℕ) : ℕ∞) < R l

/-- The first round `m ∈ [1, f + 1]` that seems clean (`NC m = NC (m - 1)`), if any. -/
noncomputable def firstClean (f : ℕ) (R : P → ℕ∞) : Option ℕ :=
  ((List.range (f + 1)).find? fun k => NC R (k + 1) = NC R k).map (· + 1)

variable {c : Context P} {f : ℕ}

/-! ### Basic properties of the records -/

@[simp] lemma ghost_zero (q l : P) : ghost c 0 q l = ⊤ := rfl

@[simp] lemma ghost_self (t : ℕ) (q : P) : ghost c t q q = ⊤ := by
  cases t <;> simp [ghost]

lemma ghost_succ_of_ne {q l : P} (h : l ≠ q) (t : ℕ) :
    ghost c (t + 1) q l = min (ghost c t q l)
      (min (if c.Deliv l q t then ⊤ else ((t + 1 : ℕ) : ℕ∞))
        (Finset.univ.inf fun y => if y ≠ q ∧ c.Deliv y q t then ghost c t y l else ⊤)) := by
  rw [ghost, ite_eq_right h]

/-- One-step characterization of `ghost c (t + 1) q l ≤ a` for a finite `a`. -/
lemma ghost_succ_le_iff {q l : P} (h : l ≠ q) {t : ℕ} {a : ℕ∞} (ha : a < ⊤) :
    ghost c (t + 1) q l ≤ a ↔ ghost c t q l ≤ a ∨ (¬ c.Deliv l q t ∧ ((t + 1 : ℕ) : ℕ∞) ≤ a) ∨
      ∃ y, y ≠ q ∧ c.Deliv y q t ∧ ghost c t y l ≤ a := by
  rw [ghost_succ_of_ne h, min_le_iff, min_le_iff, Finset.inf_le_iff ha]
  have hna : ¬ (⊤ : ℕ∞) ≤ a := not_le.2 ha
  apply or_congr_right
  apply or_congr
  · split_ifs with hd <;> simp [hd, hna]
  · simp only [Finset.mem_univ, true_and]
    refine exists_congr fun y => ?_
    split_ifs with hy <;> simp_all

/-- Records only decrease. -/
lemma ghost_succ_le (t : ℕ) (q l : P) : ghost c (t + 1) q l ≤ ghost c t q l := by
  by_cases h : l = q
  · subst h; simp
  · rw [ghost_succ_of_ne h]; exact min_le_left _ _

lemma ghost_antitone (q l : P) : Antitone fun t => ghost c t q l :=
  antitone_nat_of_succ_le fun t => ghost_succ_le t q l

/-- Missing `l`'s round-`t + 1` message makes `q` record round `t + 1` (at the latest). -/
lemma ghost_succ_le_of_not_deliv {q l : P} {t : ℕ} (h : l ≠ q) (hd : ¬ c.Deliv l q t) :
    ghost c (t + 1) q l ≤ ((t + 1 : ℕ) : ℕ∞) := by
  rw [ghost_succ_of_ne h, ite_eq_right hd]
  exact min_le_of_right_le (min_le_left _ _)

/-- **Spread.** Records travel with the messages of round `t + 1`. -/
lemma ghost_succ_le_of_deliv {q l y : P} {t : ℕ} (hlq : l ≠ q) (hyq : y ≠ q)
    (hd : c.Deliv y q t) : ghost c (t + 1) q l ≤ ghost c t y l := by
  rw [ghost_succ_of_ne hlq]
  refine min_le_of_right_le (min_le_of_right_le ((Finset.inf_le (Finset.mem_univ y)).trans ?_))
  simp [hyq, hd]

/-- **Lower bound.** Nobody records `l` as crashed before its crash round. -/
lemma crash_le_ghost {l : P} {k : ℕ} (hk : c.crash l = some k) (t : ℕ) (q : P) :
    (k : ℕ∞) ≤ ghost c t q l := by
  induction t generalizing q with
  | zero => simp
  | succ t ih =>
    by_cases h : l = q
    · subst h; simp
    rw [ghost_succ_of_ne h]
    refine le_min (ih q) (le_min ?_ (Finset.le_inf fun y _ => ?_))
    · split_ifs with hd
      · exact le_top
      · have : k ≤ t + 1 := by
          by_contra hlt
          exact hd ⟨fun m hm => by rw [hk] at hm; cases hm; omega,
            fun h => by rw [hk] at h; cases h.1; omega⟩
        exact_mod_cast this
    · split_ifs
      · exact ih y
      · exact le_top

/-- Records of nonfaulty agents are never set. -/
lemma ghost_eq_top_of_not_faulty {l : P} (hl : ¬ c.Faulty l) (t : ℕ) (q : P) :
    ghost c t q l = ⊤ := by
  have hl' : c.crash l = none := not_not.1 hl
  have hd : ∀ q t, c.Deliv l q t := fun q t => ⟨fun m hm => by simp [hl'] at hm, by simp [hl']⟩
  induction t generalizing q with
  | zero => rfl
  | succ t ih =>
    by_cases h : l = q
    · subst h; simp
    rw [ghost_succ_of_ne h, ih, ite_eq_left (hd q t)]
    simp [ih]

/-- An agent recorded as crashed is faulty. -/
lemma faulty_of_ghost_ne_top {t : ℕ} {q l : P} (h : ghost c t q l ≠ ⊤) : c.Faulty l :=
  fun hl => h (ghost_eq_top_of_not_faulty (not_not.2 hl) t q)

/-- An agent recorded as crashed by round `a` crashed in a round `k ≤ a`. -/
lemma exists_crash_of_ghost_le {t a : ℕ} {q l : P} (h : ghost c t q l ≤ a) :
    ∃ k, c.crash l = some k ∧ k ≤ a := by
  cases hk : c.crash l with
  | none =>
    rw [ghost_eq_top_of_not_faulty (by simp [Context.Faulty, hk])] at h
    simp at h
  | some k => exact ⟨k, rfl, by exact_mod_cast (crash_le_ghost hk t q).trans h⟩

/-- **Upper bound.** If `l` crashes in round `k` and `k + 1 ≤ t`, every other agent records `l`
as crashed in round `k + 1` at the latest. -/
lemma ghost_le_succ_crash {l q : P} {k t : ℕ} (hk : c.crash l = some k) (hlq : l ≠ q)
    (ht : k + 1 ≤ t) : ghost c t q l ≤ ((k + 1 : ℕ) : ℕ∞) :=
  (ghost_antitone q l ht).trans
    (ghost_succ_le_of_not_deliv hlq fun hd => (hd.1 k hk).false)

/-- All records are `≥ 1`. -/
lemma one_le_ghost (t : ℕ) (q l : P) : 1 ≤ ghost c t q l := by
  induction t generalizing q with
  | zero => simp
  | succ t ih =>
    by_cases h : l = q
    · subst h; simp
    rw [ghost_succ_of_ne h]
    refine le_min (ih q) (le_min ?_ (Finset.le_inf fun y _ => ?_))
    · split_ifs
      · exact le_top
      · exact_mod_cast Nat.succ_pos t
    · split_ifs
      · exact ih y
      · exact le_top

/-- An agent that missed `l`'s round-`1` message records `l` as crashed in round `1`. -/
lemma ghost_le_one_of_not_deliv {q l : P} (hlq : l ≠ q) (h : ¬ c.Deliv l q 0) {t : ℕ}
    (ht : 1 ≤ t) : ghost c t q l ≤ 1 :=
  (ghost_antitone q l ht).trans (by simpa using ghost_succ_le_of_not_deliv hlq h)

/-! ### Seemingly clean rounds -/

lemma mem_NC {R : P → ℕ∞} {m : ℕ} {l : P} : l ∈ NC R m ↔ (m : ℕ∞) < R l := by
  simp [NC]

lemma NC_succ_subset (R : P → ℕ∞) (k : ℕ) : NC R (k + 1) ⊆ NC R k := fun l hl => by
  rw [mem_NC] at hl ⊢
  exact lt_of_le_of_lt (by exact_mod_cast k.le_succ) hl

/-- If round `k + 1` does not seem clean, some agent is recorded as crashed exactly in it. -/
lemma exists_eq_of_NC_ne {R : P → ℕ∞} {k : ℕ} (h : NC R (k + 1) ≠ NC R k) :
    ∃ a, R a = ((k + 1 : ℕ) : ℕ∞) := by
  obtain ⟨a, ha, ha'⟩ := Finset.exists_of_ssubset (ssubset_of_subset_of_ne (NC_succ_subset R k) h)
  rw [mem_NC] at ha ha'
  refine ⟨a, le_antisymm (not_lt.1 ha') ?_⟩
  rw [Nat.cast_succ]
  exact Order.add_one_le_of_lt ha

lemma firstClean_eq_some {R : P → ℕ∞} {μ : ℕ} (h : firstClean f R = some μ) :
    ∃ k, μ = k + 1 ∧ k ≤ f ∧ NC R (k + 1) = NC R k ∧ ∀ j < k, NC R (j + 1) ≠ NC R j := by
  simp only [firstClean, Option.map_eq_some_iff, List.find?_range_eq_some, decide_eq_true_eq,
    List.mem_range, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at h
  obtain ⟨k, ⟨hk, hkf, hpre⟩, rfl⟩ := h
  exact ⟨k, rfl, by omega, hk, hpre⟩

/-- Counting faulty agents: if every round `j ∈ [1, f + 1]` is the `κ`-label of a faulty agent,
there are at least `f + 1` faulty agents. -/
lemma succ_le_card_faulty (κ : P → ℕ)
    (h : ∀ j, 1 ≤ j → j ≤ f + 1 → ∃ p, c.Faulty p ∧ κ p = j) : f + 1 ≤ c.faulty.card := by
  have := Finset.card_le_card_of_surjOn κ (s := c.faulty) (t := Finset.Icc 1 (f + 1))
    fun j hj => by
      simp only [Finset.coe_Icc, Set.mem_Icc] at hj
      obtain ⟨p, hp, rfl⟩ := h j hj.1 hj.2
      exact ⟨p, by simpa [Context.faulty] using hp, rfl⟩
  simpa using this

/-- A nonfaulty agent finds a seemingly clean round (at most `f` crashes). -/
lemma firstClean_isSome (hadm : c.Admissible f) (q : P) :
    (firstClean f (ghost c (f + 1) q)).isSome := by
  by_contra hn
  simp only [firstClean, Option.isSome_map, List.find?_isSome, List.mem_range,
    decide_eq_true_eq, not_exists, not_and] at hn
  have := succ_le_card_faulty (c := c) (f := f) (fun p => (ghost c (f + 1) q p).toNat)
    fun j hj1 hjf => by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      obtain ⟨a, ha⟩ := exists_eq_of_NC_ne (hn i (by omega))
      exact ⟨a, faulty_of_ghost_ne_top (t := f + 1) (q := q) (by simp [ha]), by simp [ha]⟩
  have := hadm.1
  omega

/-! ### Agreement -/

/-- **Crash chain.** If nonfaulty `q₁` records `l` as crashed by round `m ≤ f + 1` but nonfaulty
`q₂` does not, then `l` crashed exactly in round `m` and in each of the rounds `m + 1, …, f + 1`
some agent crashes. -/
theorem crash_chain_of_disagree {q₁ q₂ l : P} (h₁ : ¬ c.Faulty q₁) (h₂ : ¬ c.Faulty q₂) {m : ℕ}
    (hm : m ≤ f + 1) (hl₁ : ghost c (f + 1) q₁ l ≤ m) (hl₂ : ¬ ghost c (f + 1) q₂ l ≤ m) :
    c.crash l = some m ∧ ∀ s, m ≤ s → s ≤ f → ∃ y, c.crash y = some (s + 1) := by
  obtain ⟨k, hk, hkm⟩ := exists_crash_of_ghost_le hl₁
  have hlq₂ : l ≠ q₂ := by rintro rfl; exact h₂ (by simp [Context.Faulty, hk])
  obtain rfl : k = m := by
    by_contra hne
    exact hl₂ ((ghost_le_succ_crash hk hlq₂ (by omega)).trans (by exact_mod_cast (by omega)))
  refine ⟨hk, fun s hs hsf => ?_⟩
  by_contra hno
  push Not at hno
  -- from round `s + 1` on, nobody who knows (by threshold `k`) is alive
  have key : ∀ t, s ≤ t → ∀ y, ghost c t y l ≤ k → ∃ j, c.crash y = some j ∧ j ≤ t := by
    intro t hst
    induction t, hst using Nat.le_induction with
    | base =>
      intro y hy
      by_contra hal
      push Not at hal
      have hyq : y ≠ q₂ := by
        rintro rfl; exact hl₂ ((ghost_antitone y l (by omega : s ≤ f + 1)).trans hy)
      exact hl₂ ((ghost_antitone q₂ l (by omega : s + 1 ≤ f + 1)).trans
        ((ghost_succ_le_of_deliv hlq₂ hyq ⟨hal, fun h => hno y h.1⟩).trans hy))
    | succ t hst ih =>
      intro y hy
      by_contra hal
      push Not at hal
      have hly : l ≠ y := by rintro rfl; simp at hy
      rcases (ghost_succ_le_iff hly (ENat.natCast_lt_top k)).1 hy with h | ⟨-, h⟩ | ⟨z, -, hz, h⟩
      · obtain ⟨j, hj, hjt⟩ := ih y h
        have := hal j hj
        omega
      · have : t + 1 ≤ k := by exact_mod_cast h
        omega
      · obtain ⟨j, hj, hjt⟩ := ih z h
        have := hz.1 j hj
        omega
  obtain ⟨j, hj, -⟩ := key (f + 1) (by omega) q₁ hl₁
  exact h₁ (by simp [Context.Faulty, hj])

/-- No disagreement at a threshold `m` up to `q₁`'s first seemingly clean round: otherwise the
`m - 1` agents witnessing that rounds `1, …, m - 1` do not seem clean to `q₁`, and the crash
chain of `crash_chain_of_disagree`, give `f + 1` faulty agents. -/
lemma not_disagree (hadm : c.Admissible f) {q₁ q₂ l : P} (h₁ : ¬ c.Faulty q₁)
    (h₂ : ¬ c.Faulty q₂) {μ m : ℕ} (hμ : firstClean f (ghost c (f + 1) q₁) = some μ)
    (hm : m ≤ μ) (hl₁ : ghost c (f + 1) q₁ l ≤ m) (hl₂ : ¬ ghost c (f + 1) q₂ l ≤ m) : False := by
  obtain ⟨k₀, rfl, hk₀f, -, hpre⟩ := firstClean_eq_some hμ
  obtain ⟨hcl, hchain⟩ := crash_chain_of_disagree h₁ h₂ (by omega) hl₁ hl₂
  let κ : P → ℕ := fun p => match c.crash p with
    | some j => if j < m then (ghost c (f + 1) q₁ p).toNat else j
    | none => 0
  have := succ_le_card_faulty (c := c) (f := f) κ fun j hj1 hjf => by
    rcases lt_trichotomy j m with hjm | rfl | hjm
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      obtain ⟨a, ha⟩ := exists_eq_of_NC_ne (hpre i (by omega))
      obtain ⟨k, hk, hki⟩ := exists_crash_of_ghost_le ha.le
      refine ⟨a, by simp [Context.Faulty, hk], ?_⟩
      simp only [κ, hk, ha, ENat.toNat_natCast]
      rw [ite_eq_left (by omega)]
    · exact ⟨l, by simp [Context.Faulty, hcl], by simp [κ, hcl]⟩
    · obtain ⟨y, hy⟩ := hchain (j - 1) (by omega) (by omega)
      rw [Nat.sub_add_cancel (by omega)] at hy
      exact ⟨y, by simp [Context.Faulty, hy], by simp [κ, hy, not_lt.2 hjm.le]⟩
  have := hadm.1
  omega

/-- **Agreement on the decision data.** All nonfaulty agents compute the same first seemingly
clean round and the same set of agents believed alive in it. -/
theorem ghost_agree (hadm : c.Admissible f) {q₁ q₂ : P} (h₁ : ¬ c.Faulty q₁)
    (h₂ : ¬ c.Faulty q₂) :
    (firstClean f (ghost c (f + 1) q₁)).map (NC (ghost c (f + 1) q₁)) =
      (firstClean f (ghost c (f + 1) q₂)).map (NC (ghost c (f + 1) q₂)) := by
  obtain ⟨μ₁, hμ₁⟩ := Option.isSome_iff_exists.1 (firstClean_isSome hadm q₁)
  obtain ⟨μ₂, hμ₂⟩ := Option.isSome_iff_exists.1 (firstClean_isSome hadm q₂)
  have hE : ∀ m, m ≤ μ₁ → m ≤ μ₂ →
      NC (ghost c (f + 1) q₁) m = NC (ghost c (f + 1) q₂) m := by
    intro m hm₁ hm₂
    ext l
    rw [mem_NC, mem_NC, ← not_le, ← not_le, not_iff_not]
    exact ⟨fun hl => by_contra fun hl' => not_disagree hadm h₁ h₂ hμ₁ hm₁ hl hl',
      fun hl => by_contra fun hl' => not_disagree hadm h₂ h₁ hμ₂ hm₂ hl hl'⟩
  rw [hμ₁, hμ₂]
  obtain ⟨k₁, rfl, -, hc₁, hp₁⟩ := firstClean_eq_some hμ₁
  obtain ⟨k₂, rfl, -, hc₂, hp₂⟩ := firstClean_eq_some hμ₂
  obtain rfl : k₁ = k₂ := by
    rcases lt_trichotomy k₁ k₂ with h | h | h
    · refine absurd ?_ (hp₂ k₁ h)
      rw [← hE _ le_rfl (by omega), hc₁, hE _ (by omega) (by omega)]
    · exact h
    · refine absurd ?_ (hp₁ k₂ h)
      rw [hE _ (by omega) le_rfl, hc₂, ← hE _ (by omega) (by omega)]
  simp [hE _ le_rfl le_rfl]

/-! ### The paper's claim about the first crash-free round fails -/

/-- The context of `not_clean_example` (`n = 4`, `f = 2`): agents `0` and `1` crash in round `1`,
`0` still reaching `2` and `3`, `1` reaching nobody; agents `2` and `3` are nonfaulty. -/
def notCleanCtx : Context (Fin 4) where
  pref _ := true
  crash := ![some 1, some 1, none, none]
  reach := ![{2, 3}, ∅, ∅, ∅]

/-- In `notCleanCtx`, only agent `1` ever records agent `0` as crashed in round `1`. -/
lemma notCleanCtx_ghost_le_one {t : ℕ} {y : Fin 4} (h : ghost notCleanCtx t y 0 ≤ 1) : y = 1 := by
  induction t generalizing y with
  | zero => simp at h
  | succ t ih =>
    have h0y : (0 : Fin 4) ≠ y := by rintro rfl; simp at h
    rcases (ghost_succ_le_iff h0y (by simp)).1 h with h | ⟨hd, ht⟩ | ⟨z, -, hz, h⟩
    · exact ih h
    · obtain rfl : t = 0 := by
        have : t + 1 ≤ 1 := by exact_mod_cast ht
        omega
      fin_cases y <;> simp_all [Context.Deliv, notCleanCtx]
    · obtain rfl := ih h
      simp [Context.Deliv, notCleanCtx] at hz

/-- **Counterexample to a step of the proof of Theorem 2.** The paper claims that the first round
`m*` in which no agent crashes seems clean to every nonfaulty agent. In `notCleanCtx` (`f = 2`)
no agent crashes in round `2`, yet round `2` does not seem clean to the nonfaulty agent `2`:
it records only in round `2` that agent `0` crashed (in round `1`, but `0`'s round-`1` message
reached `2`), whereas agent `1` is recorded with round `1`; so `0 ∈ NC 1 \ NC 2`. -/
theorem not_clean_example :
    ∃ c : Context (Fin 4), c.Admissible 2 ∧ (∀ p, c.crash p ≠ some 2) ∧ ¬ c.Faulty 2 ∧
      NC (ghost c 3 2) 2 ≠ NC (ghost c 3 2) 1 := by
  refine ⟨notCleanCtx, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · refine (Finset.card_le_card (t := ({0, 1} : Finset (Fin 4))) fun p hp => ?_).trans (by decide)
    rw [Context.faulty, Finset.mem_filter] at hp
    fin_cases p <;> simp_all [Context.Faulty, notCleanCtx]
  · intro p m h
    fin_cases p <;> simp_all [notCleanCtx]
  · intro p
    fin_cases p <;> simp [notCleanCtx]
  · simp [Context.Faulty, notCleanCtx]
  · have h₁ : ghost notCleanCtx 3 2 0 ≤ 2 := by
      simpa using ghost_le_succ_crash (c := notCleanCtx) (k := 1) rfl (by decide) (by norm_num)
    have h₂ : ¬ ghost notCleanCtx 3 2 0 ≤ 1 := fun h => by
      simpa using notCleanCtx_ghost_le_one h
    intro h
    have := congrArg ((0 : Fin 4) ∈ ·) h
    simp only [mem_NC, eq_iff_iff, Nat.cast_ofNat, Nat.cast_one] at this
    exact not_lt.2 h₁ (this.2 (not_le.1 h₂))

end Podc.RationalConsensus
