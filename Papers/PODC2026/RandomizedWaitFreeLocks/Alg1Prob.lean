import Papers.PODC2026.RandomizedWaitFreeLocks.Alg1StepFacts
import Papers.PODC2026.RandomizedWaitFreeLocks.AdaptiveProb
import Papers.PODC2026.RandomizedWaitFreeLocks.Series

/-!
# Algorithm 1: success probability — Lemma 4.8 and Theorem 4.9

The coin of line 6 of a process `x` is `true` (write) with probability `eps b_x =
1/(7 b_x log₂²(b_x+1))`, where `b_x` is the contention observed in line 5 (`coinP`).  The
adversary is weak adaptive: it chooses each action knowing the whole history, but not the coin
of the step it schedules (`prob` of `AdaptiveProb.lean`).

We fix a process `p`, its call number `k` and the descriptor `δ` of that call, and bound the
probability of the event `Bad`: "the `k`-th `TryLock` call of `p` returns `False`".

The proof is a potential-function (supermartingale) argument replacing the paper's coupling:
* `Good` — `δ` has been promoted during the call (or the call is over without failing): the call
  cannot fail any more (Observation 4.2); potential `0`.
* `Win` — `p` has written `δ` to `R`, `δ` is still in `R` and not promoted; potential
  `1/2 − Σ_{x ∈ W} eps b_x`, where `W` are the processes whose line 6 came after `p`'s write
  (`Wset`).  By Lemma 4.5 they are all still inside lines 1–4, hence counted in `C`, and by
  Corollary 4.7 their observed contentions are pairwise distinct ranks, so the sum is
  `≤ Σ_i eps i ≤ 1/2` (`Series.lean`).  A new process executing line 6 writes with probability
  `eps b` (potential ≤ 1) or joins `W`.
* `Pre` — `p` is about to execute line 6; potential `1 − eps b_p / 2`.
-/

namespace Podc.RandomizedWaitFreeLocks.Alg1

variable {P D : Type*} [DecidableEq P] [DecidableEq D] (own : D → P)

/-- Probability that the coin of the step is `true` (only line 6 flips a coin). -/
noncomputable def coinP (c : Cfg P D) : Act P D → ℝ
  | .sched x => if (c.loc x).pc = .wr then eps (c.loc x).b else 0
  | .invoke _ _ => 0

/-- Probability that the configuration after `n` steps satisfies `E`, for the adversary `σ`. -/
noncomputable abbrev probA (σ : List (Cfg P D) → Act P D) (E : Cfg P D → Prop) (n : ℕ)
    (c : Cfg P D) : ℝ :=
  prob (fun c a b => (step own c a b).1) coinP σ E n [] c

/-- Processes whose line 6 came after the last write to `R` and that are inside lines 1–4. -/
def Wset (c : Cfg P D) : Finset P :=
  c.act.filter (fun x => (c.loc x).pc.hap = true ∧ c.lastW < (c.loc x).l6)

/-- The sum of their write probabilities. -/
noncomputable def Sig (c : Cfg P D) : ℝ := ∑ x ∈ Wset c, eps (c.loc x).b

section Potential

variable (p : P) (k : ℕ) (δ : D)

/-- The `k`-th call of `p` returned `False`. -/
def Bad (c : Cfg P D) : Prop := c.failed p k = true

/-- The call can no longer fail. -/
def Good (c : Cfg P D) : Prop :=
  c.failed p k = false ∧ (k < (c.loc p).call ∨ ((c.loc p).call = k ∧
    ((c.loc p).dsc = none ∨ ((c.loc p).dsc = some δ ∧ c.eT δ ≠ 0))))

/-- `p` wrote `δ` to `R`; still there and not promoted. -/
def Win (c : Cfg P D) : Prop :=
  c.failed p k = false ∧ c.R = some δ ∧ c.eT δ = 0 ∧ (c.loc p).dsc = some δ ∧
    (c.loc p).l6 = c.lastW ∧ (c.loc p).call = k ∧ (c.loc p).pc.hap = true

/-- `p` is about to execute line 6 of its `k`-th call, on `δ`. -/
def Pre (c : Cfg P D) : Prop :=
  c.failed p k = false ∧ (c.loc p).dsc = some δ ∧ (c.loc p).call = k ∧ (c.loc p).pc = .wr

open Classical in
/-- The potential. -/
noncomputable def V (c : Cfg P D) : ℝ :=
  if c.failed p k = true then 1
  else if Good p k δ c then 0
  else if Win p k δ c then 1 / 2 - Sig c
  else if Pre p k δ c then 1 - eps (c.loc p).b / 2
  else 1

end Potential

variable {own}

/-- Membership in `Wset` in a reachable configuration. -/
lemma mem_Wset {c : Cfg P D} (hc : Reach own c) (x : P) :
    x ∈ Wset c ↔ (c.loc x).pc.hap = true ∧ c.lastW < (c.loc x).l6 := by
  unfold Wset
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨((inv_reach own hc).act_iff x).2 ?_, h⟩
    have := h.1; revert this; cases (c.loc x).pc <;> simp [PC.hap, PC.inAct]

/-- Corollary 4.7 + the series bound: `Σ_{x ∈ W} eps b_x ≤ 1/2`. -/
lemma Sig_le {c : Cfg P D} (hc : Reach own c) : Sig c ≤ 1 / 2 := by
  have hI := inv_reach own hc
  have hsub : Wset c ⊆ c.act := Finset.filter_subset _ _
  apply sum_eps_le_half_of_rank (Wset c) (fun x => (c.loc x).fT)
  · intro x hx z hz e; exact hI.k2 x (hsub hx) z (hsub hz) e
  · intro x hx
    refine le_trans ?_ (hI.k1 x (hsub hx))
    apply Nat.add_le_add_left; apply Finset.card_le_card
    intro z hz; simp only [Finset.mem_filter] at hz ⊢; exact ⟨hsub hz.1, hz.2⟩

lemma Sig_nonneg (c : Cfg P D) : 0 ≤ Sig c :=
  Finset.sum_nonneg (fun x _ => eps_nonneg _)

section
variable {p : P} {k : ℕ} {δ : D}

lemma V_le_one {c : Cfg P D} : V p k δ c ≤ 1 := by
  unfold V
  have := Sig_nonneg c
  have := eps_nonneg (c.loc p).b
  split_ifs <;> linarith

lemma V_nonneg {c : Cfg P D} (hc : Reach own c) : 0 ≤ V p k δ c := by
  unfold V
  have := Sig_le hc
  have := eps_le_one (c.loc p).b
  split_ifs <;> linarith

lemma V_of_Good {c : Cfg P D} (h : Good p k δ c) : V p k δ c = 0 := by
  unfold V; rw [if_neg (by rw [h.1]; simp), if_pos h]

lemma V_le_of_Win {c : Cfg P D} (hc : Reach own c) (h : Win p k δ c) :
    V p k δ c ≤ 1 / 2 - Sig c := by
  unfold V; rw [if_neg (by rw [h.1]; simp)]
  have := Sig_le hc
  split_ifs <;> linarith

lemma eT_pre {c : Cfg P D} (hc : Reach own c) (h : Pre p k δ c) : c.eT δ = 0 :=
  (inv_reach own hc).eT_wr own h.2.2.2 h.2.1

lemma V_of_Pre {c : Cfg P D} (hc : Reach own c) (h : Pre p k δ c) :
    V p k δ c = 1 - eps (c.loc p).b / 2 := by
  unfold V
  rw [if_neg (by rw [h.1]; simp)]
  have hng : ¬ Good p k δ c := by
    rintro ⟨-, h1 | ⟨-, h2 | ⟨-, h3⟩⟩⟩
    · rw [h.2.2.1] at h1; exact lt_irrefl _ h1
    · rw [h.2.1] at h2; cases h2
    · exact h3 (eT_pre hc h)
  have hnw : ¬ Win p k δ c := by
    rintro ⟨-, -, -, -, -, -, h1⟩; rw [h.2.2.2] at h1; simp [PC.hap] at h1
  rw [if_neg hng, if_neg hnw, if_pos h]

end

section Steps
variable {p : P} {k : ℕ} {δ : D}

lemma step_invoke_bad (c : Cfg P D) (δ' : D) (b : Bool) (h : (c.loc p).pc ≠ .idle) :
    (step own c (.invoke p δ') b).1 = c.tick := by
  simp only [step]; rw [if_neg (fun hg => h hg.1)]

/-- `Good` is closed under steps. -/
lemma Good_step {c : Cfg P D} (hc : Reach own c) (hG : Good p k δ c) (a : Act P D) (b : Bool) :
    Good p k δ (step own c a b).1 := by
  have hI := inv_reach own hc
  obtain ⟨hf, hG⟩ := hG
  by_cases hx : p = a.actor
  · cases a with
    | invoke q δ' =>
      simp only [Act.actor] at hx; subst hx
      refine ⟨by rw [step_invoke_failed]; exact hf, ?_⟩
      simp only [step]
      split_ifs with hg
      · left; simp only [Cfg.tick, Cfg.upd, Function.update_apply]
        rcases hG with h | ⟨h, -⟩ <;> simp <;> omega
      · exact hG
    | sched q =>
      simp only [Act.actor] at hx; subst hx
      obtain ⟨hcall, -, -⟩ := step_sched_fixed own c p b
      by_cases hr : (c.loc p).pc = .ret
      · obtain ⟨hd, hfl⟩ := step_ret own c p b hr
        refine ⟨?_, ?_⟩
        · cases e : (step own c (.sched p) b).1.failed p k
          · rfl
          · rcases hfl k e with h | ⟨rfl, d, hd', hdn⟩
            · rw [hf] at h; cases h
            · exfalso
              rcases hG with h | ⟨-, h | ⟨h1, h2⟩⟩
              · exact lt_irrefl _ h
              · rw [h] at hd'; cases hd'
              · rw [h1] at hd'; cases hd'
                have := hI.o2 δ h2 (by rw [hI.own_dsc p δ h1]; exact h1)
                  (by rw [hI.own_dsc p δ h1]; exact Or.inr hr)
                rw [this] at hdn; cases hdn
        · rw [hcall]
          rcases hG with h | ⟨h, -⟩
          · exact Or.inl h
          · exact Or.inr ⟨h, Or.inl hd⟩
      · refine ⟨by rw [step_sched_failed own c p b hr]; exact hf, ?_⟩
        rw [hcall, step_sched_dsc own c p b hr]
        rcases hG with h | ⟨h, h' | ⟨h1, h2⟩⟩
        · exact Or.inl h
        · exact Or.inr ⟨h, Or.inl h'⟩
        · exact Or.inr ⟨h, Or.inr ⟨h1, step_eT_ne own c _ b δ h2⟩⟩
  · refine ⟨by rw [step_failed_ne own c a b p hx]; exact hf, ?_⟩
    rw [step_loc_ne own c a b p hx]
    rcases hG with h | ⟨h, h' | ⟨h1, h2⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, Or.inl h'⟩
    · exact Or.inr ⟨h, Or.inr ⟨h1, step_eT_ne own c a b δ h2⟩⟩

/-- Generic description of the local state of a process after a step in which it does not
execute line 6, line 10, nor start a call. -/
lemma step_loc_quiet {c : Cfg P D} (a : Act P D) (b : Bool) (y : P)
    (hy : (c.loc y).pc ≠ .idle) (hwr : (c.loc y).pc ≠ .wr) (hret : (c.loc y).pc ≠ .ret) :
    ((step own c a b).1.loc y).dsc = (c.loc y).dsc ∧
    ((step own c a b).1.loc y).call = (c.loc y).call ∧
    ((step own c a b).1.loc y).b = (c.loc y).b ∧
    ((step own c a b).1.loc y).l6 = (c.loc y).l6 ∧
    (step own c a b).1.failed y = c.failed y ∧
    (((step own c a b).1.loc y).pc.hap = true → (c.loc y).pc.hap = true) ∧
    ((c.loc y).pc.hap = true → ((step own c a b).1.loc y).pc.hap = true ∨
      ((step own c a b).1.loc y).pc = .rd8) := by
  by_cases hx : y = a.actor
  · cases a with
    | invoke q δ' =>
      simp only [Act.actor] at hx; subst hx
      rw [step_invoke_bad c δ' b hy]; exact ⟨rfl, rfl, rfl, rfl, rfl, id, Or.inl⟩
    | sched q =>
      simp only [Act.actor] at hx; subst hx
      obtain ⟨h1, h2, -⟩ := step_sched_fixed own c y b
      exact ⟨step_sched_dsc own c y b hret, h1, h2, step_sched_l6 own c y b hwr,
        congrFun (step_sched_failed own c y b hret) y, (step_sched_hap own c y b hwr).1,
        (step_sched_hap own c y b hwr).2⟩
  · rw [step_loc_ne own c a b y hx, step_failed_ne own c a b y hx]
    exact ⟨rfl, rfl, rfl, rfl, rfl, id, Or.inl⟩

/-- A step of the window that is not a line-6 step: either `δ` gets promoted (`Good`) or the
window persists with the same set `W`. -/
lemma Win_step {c : Cfg P D} (hc : Reach own c) (hW : Win p k δ c) (a : Act P D) (b : Bool)
    (hnw : ∀ q, a = .sched q → (c.loc q).pc ≠ .wr) :
    Good p k δ (step own c a b).1 ∨
      (Win p k δ (step own c a b).1 ∧ Sig (step own c a b).1 = Sig c) := by
  have hI := inv_reach own hc
  have hc' : Reach own (step own c a b).1 :=
    Reachable.of_step (init := init) (step := step own) hc a b
  have hI' := inv_reach own hc'
  set c' := (step own c a b).1 with hc'def
  obtain ⟨hf, hR, he, hd, hl6, hcall, hhap⟩ := hW
  obtain ⟨hR', hW'⟩ := step_RW own c a b (by rintro ⟨q, rfl, hq, -⟩; exact hnw q rfl hq)
  have hpidle : (c.loc p).pc ≠ .idle := by intro h; rw [h] at hhap; simp [PC.hap] at hhap
  have hpwr : (c.loc p).pc ≠ .wr := by intro h; rw [h] at hhap; simp [PC.hap] at hhap
  have hpret : (c.loc p).pc ≠ .ret := by intro h; rw [h] at hhap; simp [PC.hap] at hhap
  obtain ⟨pd, pc, -, pl6, pf, -, ph⟩ := step_loc_quiet (own := own) a b p hpidle hpwr hpret
  have hpast : ((c'.loc p).pc.hap || (c'.loc p).pc.post) = true := by
    rcases ph hhap with h | h
    · rw [hc'def, h]; rfl
    · rw [hc'def, h]; simp [PC.post]
  by_cases he' : c'.eT δ = 0
  · right
    have hWin : Win p k δ c' := by
      refine ⟨by rw [pf]; exact hf, by rw [hR', hR], he', by rw [pd, hd],
        by rw [pl6, hl6, hW'], by rw [pc, hcall], ?_⟩
      exact hI'.g1 p δ (by rw [hR', hR]) he' hpast (by rw [pl6, hl6, hW'])
    refine ⟨hWin, ?_⟩
    -- the set `W` does not change
    have hmem : ∀ y, y ∈ Wset c' ↔ y ∈ Wset c := by
      intro y
      rw [mem_Wset hc', mem_Wset hc, hW']
      by_cases hy : y = a.actor
      · cases a with
        | invoke q δ' =>
          simp only [Act.actor] at hy; subst hy
          by_cases hidle : (c.loc y).pc = .idle
          · simp only [hidle, PC.hap, Bool.false_eq_true, false_and, iff_false]
            simp only [c', step]
            split_ifs <;> simp [Cfg.tick, Cfg.upd, hidle, PC.hap]
          · rw [hc'def, step_invoke_bad c δ' b hidle]; simp [Cfg.tick]
        | sched q =>
          simp only [Act.actor] at hy; subst hy
          have hwr := hnw y rfl
          rw [step_sched_l6 own c y b hwr]
          obtain ⟨h1, h2⟩ := step_sched_hap own c y b hwr
          constructor
          · rintro ⟨h3, h4⟩; exact ⟨h1 h3, h4⟩
          · rintro ⟨h3, h4⟩
            refine ⟨?_, h4⟩
            rcases h2 h3 with h5 | h5
            · exact h5
            · exact hI'.g1 y δ (by rw [hR', hR]) he' (by rw [h5]; simp [PC.post])
                (by rw [hW', step_sched_l6 own c y b hwr]; omega)
      · rw [step_loc_ne own c a b y hy]
    have hWeq : Wset c' = Wset c := Finset.ext hmem
    unfold Sig
    rw [hWeq]
    apply Finset.sum_congr rfl
    intro y hy
    rw [mem_Wset hc] at hy
    have hyi : (c.loc y).pc ≠ .idle := by intro h; rw [h] at hy; simp [PC.hap] at hy
    have hyw : (c.loc y).pc ≠ .wr := by intro h; rw [h] at hy; simp [PC.hap] at hy
    have hyr : (c.loc y).pc ≠ .ret := by intro h; rw [h] at hy; simp [PC.hap] at hy
    rw [(step_loc_quiet (own := own) a b y hyi hyw hyr).2.2.1]
  · left
    exact ⟨by rw [pf]; exact hf, Or.inr ⟨by rw [pc, hcall], Or.inr ⟨by rw [pd, hd], he'⟩⟩⟩

/-- A line-6 step without write of another process during the window: the window persists and
the process joins `W`. -/
lemma Win_wr0 {c : Cfg P D} (hc : Reach own c) (hW : Win p k δ c) {q : P}
    (hq : (c.loc q).pc = .wr) :
    Win p k δ (step own c (.sched q) false).1 ∧
      Sig (step own c (.sched q) false).1 = Sig c + eps (c.loc q).b := by
  have hI := inv_reach own hc
  have hc' : Reach own (step own c (.sched q) false).1 :=
    Reachable.of_step (init := init) (step := step own) hc _ _
  obtain ⟨hf, hR, he, hd, hl6, hcall, hhap⟩ := hW
  have hqp : q ≠ p := by rintro rfl; rw [hq] at hhap; simp [PC.hap] at hhap
  have hstep : (step own c (.sched q) false).1 =
      c.tick.upd q { c.loc q with pc := .rdL false, l6 := c.T + 1 } := by
    simp [step, hq]
  rw [hstep] at hc' ⊢
  refine ⟨⟨by simpa [Cfg.tick, Cfg.upd] using hf, by simpa using hR, by simpa using he,
    by simpa [Ne.symm hqp] using hd, by simpa [Ne.symm hqp] using hl6,
    by simpa [Ne.symm hqp] using hcall, by simpa [Ne.symm hqp] using hhap⟩, ?_⟩
  have hqW : q ∉ Wset c := by rw [mem_Wset hc, hq]; simp [PC.hap]
  have hmem : Wset (c.tick.upd q { c.loc q with pc := .rdL false, l6 := c.T + 1 }) =
      insert q (Wset c) := by
    ext y
    rw [mem_Wset hc', Finset.mem_insert, mem_Wset hc]
    by_cases hy : y = q
    · subst hy; simp [PC.hap]; have := hI.lastW_le; omega
    · simp [hy]
  unfold Sig
  rw [hmem, Finset.sum_insert hqW]
  simp only [upd_loc, if_pos rfl, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  have : y ≠ q := fun e => hqW (e ▸ hy)
  simp [this]

/-- Before `p`'s line 6, steps of other processes keep `Pre` and `b_p`. -/
lemma Pre_step {c : Cfg P D} (hc : Reach own c) (hP : Pre p k δ c) (a : Act P D) (b : Bool)
    (ha : a ≠ .sched p) :
    Pre p k δ (step own c a b).1 ∧ ((step own c a b).1.loc p).b = (c.loc p).b := by
  obtain ⟨hf, hd, hcall, hwr⟩ := hP
  by_cases hx : p = a.actor
  · cases a with
    | invoke q δ' =>
      simp only [Act.actor] at hx; subst hx
      rw [step_invoke_bad c δ' b (by rw [hwr]; simp)]
      exact ⟨⟨hf, hd, hcall, hwr⟩, rfl⟩
    | sched q => simp only [Act.actor] at hx; subst hx; exact absurd rfl ha
  · have hl := step_loc_ne own c a b p hx
    have hfl := step_failed_ne own c a b p hx
    exact ⟨⟨by rw [hfl]; exact hf, by rw [hl]; exact hd, by rw [hl]; exact hcall,
      by rw [hl]; exact hwr⟩, by rw [hl]⟩

/-- `p`'s line 6 with a write opens the window, with `W = ∅`. -/
lemma Pre_wr1 {c : Cfg P D} (hc : Reach own c) (hP : Pre p k δ c) :
    Win p k δ (step own c (.sched p) true).1 ∧ Sig (step own c (.sched p) true).1 = 0 := by
  have hI := inv_reach own hc
  have hc' : Reach own (step own c (.sched p) true).1 :=
    Reachable.of_step (init := init) (step := step own) hc _ _
  obtain ⟨hf, hd, hcall, hwr⟩ := hP
  have he := hI.eT_wr own hwr hd
  have hstep : (step own c (.sched p) true).1 =
      { (c.tick.upd p { c.loc p with pc := .rdL false, l6 := c.T + 1 }) with
        R := (c.loc p).dsc, lastW := c.T + 1 } := by
    simp [step, hwr]
  rw [hstep] at hc' ⊢
  refine ⟨⟨by simpa [Cfg.tick, Cfg.upd] using hf, by simpa using hd, by simpa [Cfg.tick, Cfg.upd] using he,
    by simpa using hd, by simp, by simpa using hcall, by simp [PC.hap]⟩, ?_⟩
  unfold Sig
  convert Finset.sum_empty
  rw [Finset.eq_empty_iff_forall_notMem]
  intro y hy
  rw [mem_Wset hc'] at hy
  obtain ⟨h1, h2⟩ := hy
  by_cases hyp : y = p
  · subst hyp; simp at h2
  · simp only [upd_loc, if_neg hyp] at h1 h2
    have h1' : (c.loc y).pc.hap = true := by simpa [Cfg.tick] using h1
    have := hI.l6_le y (by simp [h1'])
    simp [Cfg.tick] at h2; omega

lemma coinP_bounds (c : Cfg P D) (a : Act P D) : 0 ≤ coinP c a ∧ coinP c a ≤ 1 := by
  cases a with
  | invoke q δ' => simp [coinP]
  | sched q =>
    simp only [coinP]
    split_ifs
    · exact ⟨eps_nonneg _, eps_le_one _⟩
    · simp

lemma coinP_zero (c : Cfg P D) (a : Act P D) (h : ∀ q, a = .sched q → (c.loc q).pc ≠ .wr) :
    coinP c a = 0 := by
  cases a with
  | invoke q δ' => rfl
  | sched q => simp [coinP, h q rfl]

/-- The potential is a supersolution: no action increases its expectation. -/
lemma V_super {c : Cfg P D} (hc : Reach own c) (a : Act P D) :
    coinP c a * V p k δ (step own c a true).1 + (1 - coinP c a) * V p k δ (step own c a false).1
      ≤ V p k δ c := by
  obtain ⟨hπ0, hπ1⟩ := coinP_bounds c a
  have ht1 : V p k δ (step own c a true).1 ≤ 1 := V_le_one
  have hf1 : V p k δ (step own c a false).1 ≤ 1 := V_le_one
  have hreach : ∀ b, Reach own (step own c a b).1 :=
    fun b => Reachable.of_step (init := init) (step := step own) hc a b
  by_cases hfail : c.failed p k = true
  · have : V p k δ c = 1 := by unfold V; rw [if_pos hfail]
    rw [this]; nlinarith
  by_cases hG : Good p k δ c
  · rw [V_of_Good hG, V_of_Good (Good_step hc hG a true), V_of_Good (Good_step hc hG a false)]
    simp
  by_cases hW : Win p k δ c
  · have hV : V p k δ c = 1 / 2 - Sig c := by
      unfold V; rw [if_neg hfail, if_neg hG, if_pos hW]
    rw [hV]
    by_cases hq : ∃ q, a = .sched q ∧ (c.loc q).pc = .wr
    · obtain ⟨q, rfl, hq⟩ := hq
      have hπ : coinP c (.sched q) = eps (c.loc q).b := by simp [coinP, hq]
      rw [hπ]
      obtain ⟨hW', hS'⟩ := Win_wr0 hc hW hq
      have h1 := V_le_of_Win (hreach false) hW'
      have h2 := Sig_le (hreach false)
      rw [hS'] at h1 h2
      have h3 := eps_nonneg (c.loc q).b
      nlinarith
    · push_neg at hq
      have hz := coinP_zero c a (fun q h => hq q h)
      rw [hz]
      have : V p k δ (step own c a false).1 ≤ 1 / 2 - Sig c := by
        rcases Win_step hc hW a false (fun q h => hq q h) with h | ⟨h, hs⟩
        · rw [V_of_Good h]; have := Sig_le hc; linarith
        · rw [← hs]; exact V_le_of_Win (hreach false) h
      linarith
  by_cases hP : Pre p k δ c
  · rw [V_of_Pre hc hP]
    by_cases ha : a = .sched p
    · subst ha
      have hπ : coinP c (.sched p) = eps (c.loc p).b := by simp [coinP, hP.2.2.2]
      rw [hπ]
      obtain ⟨hW', hS'⟩ := Pre_wr1 hc hP
      have h1 := V_le_of_Win (hreach true) hW'
      rw [hS'] at h1
      have := eps_nonneg (c.loc p).b
      nlinarith
    · obtain ⟨hPt, hbt⟩ := Pre_step hc hP a true ha
      obtain ⟨hPf, hbf⟩ := Pre_step hc hP a false ha
      rw [V_of_Pre (hreach true) hPt, V_of_Pre (hreach false) hPf, hbt, hbf]
      ring_nf; linarith
  · have : V p k δ c = 1 := by
      unfold V; rw [if_neg hfail, if_neg hG, if_neg hW, if_neg hP]
    rw [this]; nlinarith

/-- The potential bounds the probability of `Bad` for every adversary and horizon. -/
lemma prob_bad_le_V {c : Cfg P D} (hc : Reach own c) (σ : List (Cfg P D) → Act P D) (n : ℕ) :
    probA own σ (Bad p k) n c ≤ V p k δ c := by
  refine prob_le_of_super (fun c a b => (step own c a b).1) coinP (Bad p k) (Reach own)
    (V p k δ) (fun c a b hc => Reachable.of_step (init := init) (step := step own) hc a b)
    (fun c a _ => coinP_bounds c a) ?_ (fun c hc => V_nonneg hc)
    (fun c a hc => V_super hc a) σ n [] c hc
  intro c _ hb
  unfold V Bad at *; rw [if_pos hb]

end Steps

/-- **Lemma 4.8.** If process `p` writes its descriptor to `R` in line 6 of a `TryLock` call,
then, for every weak adaptive adversary and every horizon `n`, the probability that this call
returns `False` within `n` further steps is at most `1/2`. -/
theorem lemma_4_8 {c : Cfg P D} (hc : Reach own c) {p : P} {δ : D}
    (hwr : (c.loc p).pc = .wr) (hd : (c.loc p).dsc = some δ)
    (σ : List (Cfg P D) → Act P D) (n : ℕ) :
    probA own σ (Bad p (c.loc p).call) n (step own c (.sched p) true).1 ≤ 1 / 2 := by
  have hf : c.failed p (c.loc p).call = false := by
    cases e : c.failed p (c.loc p).call
    · rfl
    · have := ((failInv_reach own hc) p _ e).2 rfl; rw [hwr] at this; cases this
  have hP : Pre p (c.loc p).call δ c := ⟨hf, hd, rfl, hwr⟩
  have hc1 : Reach own (step own c (.sched p) true).1 :=
    Reachable.of_step (init := init) (step := step own) hc _ _
  obtain ⟨hW, hS⟩ := Pre_wr1 hc hP
  calc probA own σ (Bad p (c.loc p).call) n (step own c (.sched p) true).1
      ≤ V p (c.loc p).call δ (step own c (.sched p) true).1 := prob_bad_le_V hc1 σ n
    _ ≤ 1 / 2 - Sig (step own c (.sched p) true).1 := V_le_of_Win hc1 hW
    _ = 1 / 2 := by rw [hS]; ring

/-- **Theorem 4.9.** Let process `p` invoke `TryLock(δ)` (step `c → c₁`), and let `S` be any
finite set containing every process with a pending call at `c₁` (so `|S|` can be the point
contention `κ` at the invocation).  For every weak adaptive adversary and every horizon `n`,
the call returns `False` within `n` steps with probability at most
`1 − 1/(14 κ log₂²(κ+1))`: each `TryLock` succeeds with probability
`Ω(1/(κ log²(κ+1)))` once it terminates. -/
theorem theorem_4_9 {c : Cfg P D} (hc : Reach own c) {p : P} {δ : D}
    (hidle : (c.loc p).pc = .idle) (hown : own δ = p) (hr : c.retT δ = false) (b₀ : Bool)
    (S : Finset P)
    (hS : ∀ x, ((step own c (.invoke p δ) b₀).1.loc x).pc ≠ .idle → x ∈ S)
    (σ : List (Cfg P D) → Act P D) (n : ℕ) :
    probA own σ (Bad p ((step own c (.invoke p δ) b₀).1.loc p).call) n
        (step own c (.invoke p δ) b₀).1 ≤
      1 - 1 / (14 * S.card * (Real.logb 2 (S.card + 1)) ^ 2) := by
  set c₁ := (step own c (.invoke p δ) b₀).1 with hc₁
  have hc1 : Reach own c₁ := Reachable.of_step (init := init) (step := step own) hc _ _
  have hI1 := inv_reach own hc1
  have hstep : c₁ = { (c.tick.upd p
      { (c.loc p) with
        pc := .wr, dsc := some δ, b := c.C + 1, fT := c.T + 1,
        call := (c.loc p).call + 1, cidx := c.T }) with
      C := c.C + 1, act := insert p c.act } := by
    rw [hc₁]; simp only [step]; rw [if_pos ⟨hidle, hown, hr⟩]
  have hloc : c₁.loc p = { (c.loc p) with
        pc := .wr, dsc := some δ, b := c.C + 1, fT := c.T + 1,
        call := (c.loc p).call + 1, cidx := c.T } := by rw [hstep]; simp
  set k := (c₁.loc p).call
  have hf : c₁.failed p k = false := by
    cases e : c₁.failed p k
    · rfl
    · have := ((failInv_reach own hc1) p _ e).2 rfl; rw [hloc] at this; cases this
  have hP : Pre p k δ c₁ := ⟨hf, by rw [hloc], rfl, by rw [hloc]⟩
  have hV := V_of_Pre hc1 hP
  -- the observed contention is at most `|S|`
  have hb : (c₁.loc p).b = c₁.act.card := by
    rw [hloc, hI1.C_eq.symm, hstep]
  have hbS : (c₁.loc p).b ≤ S.card := by
    rw [hb]; apply Finset.card_le_card
    intro x hx
    apply hS x
    have := (hI1.act_iff x).1 hx
    intro h; rw [h] at this; simp [PC.inAct] at this
  have hb1 : 1 ≤ (c₁.loc p).b := by rw [hloc]; simp
  have hmono := eps_antitone hb1 hbS
  have hpb := prob_bad_le_V (p := p) (k := k) (δ := δ) hc1 σ n
  have heq : eps S.card / 2 = 1 / (14 * S.card * (Real.logb 2 (S.card + 1)) ^ 2) := by
    unfold eps; rw [div_div]; ring_nf
  calc probA own σ (Bad p k) n c₁ ≤ V p k δ c₁ := hpb
    _ = 1 - eps (c₁.loc p).b / 2 := hV
    _ ≤ 1 - eps S.card / 2 := by linarith
    _ = _ := by rw [heq]

end Podc.RandomizedWaitFreeLocks.Alg1
