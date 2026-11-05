import Papers.PODC2019.RMESubLogBoth.LiveRepair3

/-!
# Liveness, part 2 (end): the recovery code and `RLock` terminate

After the last crash, eventually (and forever after) no process is in the recovery code
(lines 10, 16–24) or in the critical section of `RLock`, and `RLock` is free
(`eventually_no_rec`).
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

/-- No step enters the recovery/`RLock` region (only a crash does). -/
lemma rec_step {c c' : Cfg k} {own : ℕ → ℕ} {p : Fin k} (hL : LI c own p) (hs : Step c p c')
    (hp : ¬ (c.pc p).Rec) : ¬ (c'.pc p).Rec := by
  unfold LI at hL
  cases hpc : c.pc p with
  | rem =>
    rw [hpc] at hL
    rcases step_l10 hs (.inl hpc) with ⟨-, h'⟩ | ⟨x, hn, -⟩
    · simp [h', PC.Rec, PC.isRec]
    · rw [hL] at hn; cases hn
  | l11 => simp [step_l11 hs hpc, PC.Rec, PC.isRec]
  | l13 x => simp [step_l13 hs hpc, PC.Rec, PC.isRec]
  | l14 x m => simp [step_l14 hs hpc, PC.Rec, PC.isRec]
  | l15 x m => simp [step_l15 hs hpc, PC.Rec, PC.isRec]
  | l25 x v =>
    rw [hpc] at hL
    obtain ⟨-, -, ⟨m, rfl⟩, -⟩ := hL
    rcases step_l25 hs hpc with ⟨-, h'⟩ | ⟨-, rfl⟩
    · simp [h', PC.Rec, PC.isRec]
    · simp [hpc, PC.Rec, PC.isRec]
  | l26 x => simp [step_l26 hs hpc, PC.Rec, PC.isRec]
  | cs x => simp [step_cs hs hpc, PC.Rec, PC.isRec]
  | l28 x => simp [step_l28 hs hpc, PC.Rec, PC.isRec]
  | l29 => simp [step_l29 hs hpc, PC.Rec, PC.isRec]
  | _ => simp [hpc, PC.Rec, PC.isRec] at hp

/-- The processes in the recovery/`RLock` region. -/
def RecS (c : Cfg k) : Finset (Fin k) := Finset.univ.filter (fun q => (c.pc q).Rec)

lemma mem_RecS {c : Cfg k} {q : Fin k} : q ∈ RecS c ↔ (c.pc q).Rec := by simp [RecS]

lemma RecS_step {c c' : Cfg k} (hI : Inv c) {p : Fin k} (hs : Step c p c') : RecS c' ⊆ RecS c := by
  obtain ⟨own, -, hL⟩ := hI
  intro q hq
  rw [mem_RecS] at hq ⊢
  by_contra hn
  by_cases hqp : q = p
  · subst hqp; exact rec_step (hL q) hs hn hq
  · rw [Step.pc_other hs hqp] at hq; exact hn hq

/-- In the setting `Good`, if somebody is in the region, there is a driver. -/
lemma Good.exists_drv {c : Cfg k} (hc : Good c) (hne : (RecS c).Nonempty) :
    ∃ p, Drv c p ∧ c.pc p ≠ .rem := by
  have hpos : ∀ {h : Fin k}, c.holder = some h → _ := fun hh => hc.holder_pos hh
  obtain ⟨⟨own, hG, hL⟩, -, h0⟩ := hc
  cases hhc : c.holder with
  | none =>
    obtain ⟨q, hq⟩ := hne
    rw [mem_RecS] at hq
    rcases rec_cases (h0 q) hq with hR | ⟨y, v, hpc⟩
    · have := hG.holder q hR; rw [hhc] at this; cases this
    · exact ⟨q, (Drv_none hhc).2 ⟨y, v, hpc⟩, by simp [hpc]⟩
  | some h =>
    by_cases hb : ∃ x tl V E i a, c.pc h = .l35 x tl V E i a ∧ c.nn a = false
    · obtain ⟨x, tl, V, E, i, a, hpc, hna⟩ := hb
      have hLh := hL h; unfold LI at hLh; rw [hpc] at hLh
      obtain ⟨-, -, -, -, EA, -, -, ha, -⟩ := hLh
      obtain ⟨o, ho, hf⟩ := owner_of_nn hG hL h0 ha hna
      refine ⟨o, (Drv_some hhc).2 (.inl ⟨x, tl, V, E, i, a, hpc, hna, ho⟩), fun hr => ?_⟩
      rw [hr] at hf; simp [f13] at hf
    · refine ⟨h, (Drv_some hhc).2 (.inr ⟨rfl, fun x tl V E i a hpc => ?_⟩), fun hr => ?_⟩
      · by_contra hn; exact hb ⟨x, tl, V, E, i, a, hpc, by simpa using hn⟩
      · rcases hpos hhc with hR | ⟨y, v, hpc⟩
        · rw [hr] at hR; exact hR
        · rw [hr] at hpc; cases hpc

/-- A ranking argument with a driver predicate: if, until `Goal` holds, the rank never increases,
some driver is not idle, every event of a driver decreases the rank, and a driver stays a driver
while it takes no step and the rank does not change, then `Goal` eventually holds. -/
lemma eventually_of_rank' (r : Run k) (hF : Fair r) (μ : ℕ → ℕ) (Goal : ℕ → Prop)
    (D : ℕ → Fin k → Prop) (T : ℕ)
    (hmono : ∀ t, T ≤ t → ¬ Goal t → ¬ Goal (t + 1) → μ (t + 1) ≤ μ t)
    (hd : ∀ t, T ≤ t → ¬ Goal t → ∃ p, D t p ∧ (r.cfg t).pc p ≠ .rem)
    (hdstep : ∀ t p, T ≤ t → ¬ Goal t → D t p → (r.ev t = .step p ∨ r.ev t = .crash p) →
      ¬ Goal (t + 1) → μ (t + 1) < μ t)
    (hdsame : ∀ t p, T ≤ t → ¬ Goal t → ¬ Goal (t + 1) → D t p → r.ev t ≠ .step p →
      r.ev t ≠ .crash p → μ (t + 1) = μ t → D (t + 1) p) :
    ∃ t, T ≤ t ∧ Goal t := by
  by_contra hno
  push Not at hno
  have key : ∀ n, ∀ t, T ≤ t → μ t ≤ n → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro t ht hμ
      obtain ⟨p, hDp, hrem⟩ := hd t ht (hno t ht)
      obtain ⟨t', htt', hev⟩ := hF p t hrem
      have : ∀ s, t ≤ s → s ≤ t' → μ s < μ t ∨ (μ s = μ t ∧ D s p) := by
        intro s hs hs'
        induction s, hs using Nat.le_induction with
        | base => exact .inr ⟨rfl, hDp⟩
        | succ s hs ihs =>
          have hle := hmono s (by omega) (hno s (by omega)) (hno (s + 1) (by omega))
          rcases ihs (by omega) with h | ⟨h1, h2⟩
          · exact .inl (lt_of_le_of_lt hle h)
          · by_cases hevs : r.ev s = .step p ∨ r.ev s = .crash p
            · exact .inl ((hdstep s p (by omega) (hno s (by omega)) h2 hevs
                (hno (s + 1) (by omega))).trans_eq h1)
            · push Not at hevs
              rcases lt_or_eq_of_le hle with h3 | h3
              · exact .inl (h3.trans_eq h1)
              · exact .inr ⟨h3.trans h1, hdsame s p (by omega) (hno s (by omega))
                  (hno (s + 1) (by omega)) h2 hevs.1 hevs.2 h3⟩
      rcases this t' htt' le_rfl with h | ⟨h1, h2⟩
      · exact ih (μ t') (by omega) t' (by omega) le_rfl
      · have h3 := hdstep t' p (by omega) (hno t' (by omega)) h2 hev (hno (t' + 1) (by omega))
        exact ih (μ (t' + 1)) (by omega) (t' + 1) (by omega) le_rfl
  exact key (μ T) T le_rfl le_rfl

/-- **Termination of the recovery code and of `RLock`.** In a fair run, after the last crash,
eventually (and forever after) no process is in the recovery code (lines 10, 16–24) or in the
critical section of `RLock`, and `RLock` is free. -/
theorem eventually_no_rec (r : Run k) (hF : Fair r) {T : ℕ} (hT : CrashFreeFrom r T)
    (p0 : Fin k) :
    ∃ T1, T ≤ T1 ∧ ∀ t, T1 ≤ t → (∀ q, ¬ ((r.cfg t).pc q).Rec) ∧ (r.cfg t).holder = none := by
  have hinv : ∀ t, Inv (r.cfg t) := fun t => inv_reach (r.reach t)
  obtain ⟨T0, hT0, hpre⟩ := eventually_no_pre r hF hinv hT p0
  have hgood : ∀ t, T0 ≤ t → Good (r.cfg t) := fun t ht =>
    ⟨hinv t, holderOK_reach (r.reach t), hpre t ht⟩
  have hstep : ∀ t, T ≤ t → ∃ p, Step (r.cfg t) p (r.cfg (t + 1)) ∧ r.ev t = .step p := by
    intro t ht
    have hn := r.next t
    cases he : r.ev t with
    | step p => rw [he] at hn; exact ⟨p, hn, rfl⟩
    | crash p => exact absurd he (hT t ht p)
  have hmonoR : ∀ t, T ≤ t → RecS (r.cfg (t + 1)) ⊆ RecS (r.cfg t) := by
    intro t ht
    obtain ⟨p, hs, -⟩ := hstep t ht
    exact RecS_step (hinv t) hs
  have hmonoR' : ∀ t t', T ≤ t → t ≤ t' → RecS (r.cfg t') ⊆ RecS (r.cfg t) := by
    intro t t' ht htt'
    induction t', htt' using Nat.le_induction with
    | base => exact le_rfl
    | succ s hs ih => exact (hmonoR s (by omega)).trans ih
  -- the region eventually shrinks
  have hdec : ∀ t0, T0 ≤ t0 → (RecS (r.cfg t0)).Nonempty →
      ∃ t, t0 ≤ t ∧ (RecS (r.cfg t)).card < (RecS (r.cfg t0)).card := by
    intro t0 ht0 hne
    have heqR : ∀ t, t0 ≤ t → ¬ (RecS (r.cfg t)).card < (RecS (r.cfg t0)).card →
        RecS (r.cfg t) = RecS (r.cfg t0) := fun t ht hg =>
      Finset.eq_of_subset_of_card_le (hmonoR' t0 t (by omega) ht) (not_lt.mp hg)
    refine eventually_of_rank' r hF (fun t => μc (r.cfg t))
      (fun t => (RecS (r.cfg t)).card < (RecS (r.cfg t0)).card) (fun t p => Drv (r.cfg t) p) t0
      ?_ ?_ ?_ ?_
    · intro t ht hg hg'
      obtain ⟨p, hs, -⟩ := hstep t (by omega)
      refine (rank_step (hgood t (by omega)) (hgood (t + 1) (by omega)) hs ?_).1
      intro q hq
      rw [← mem_RecS] at hq ⊢
      rw [heqR (t + 1) (by omega) hg']; rw [heqR t ht hg] at hq; exact hq
    · intro t ht hg
      refine (hgood t (by omega)).exists_drv ?_
      rw [heqR t ht hg]; exact hne
    · intro t p ht hg hD hev hg'
      obtain ⟨p', hs, he⟩ := hstep t (by omega)
      rcases hev with hev | hev
      · rw [hev] at he; cases he
        refine (rank_step (hgood t (by omega)) (hgood (t + 1) (by omega)) hs ?_).2.1 hD
        intro q hq
        rw [← mem_RecS] at hq ⊢
        rw [heqR (t + 1) (by omega) hg']; rw [heqR t ht hg] at hq; exact hq
      · rw [hev] at he; cases he
    · intro t p ht hg hg' hD hev _ hμ
      obtain ⟨p', hs, he⟩ := hstep t (by omega)
      have hpp : p ≠ p' := by rintro rfl; exact hev he
      refine (rank_step (hgood t (by omega)) (hgood (t + 1) (by omega)) hs ?_).2.2 p hpp hD hμ
      intro q hq
      rw [← mem_RecS] at hq ⊢
      rw [heqR (t + 1) (by omega) hg']; rw [heqR t ht hg] at hq; exact hq
  -- hence it eventually becomes empty
  have hempty : ∀ n, ∀ t0, T0 ≤ t0 → (RecS (r.cfg t0)).card ≤ n →
      ∃ t1, t0 ≤ t1 ∧ RecS (r.cfg t1) = ∅ := by
    intro n
    induction n with
    | zero => intro t0 _ h; exact ⟨t0, le_rfl, Finset.card_eq_zero.mp (by omega)⟩
    | succ n ih =>
      intro t0 ht0 h
      by_cases he : RecS (r.cfg t0) = ∅
      · exact ⟨t0, le_rfl, he⟩
      · obtain ⟨t, htt, hlt⟩ := hdec t0 ht0 (Finset.nonempty_iff_ne_empty.mpr he)
        obtain ⟨t1, ht1, h1⟩ := ih t (by omega) (by omega)
        exact ⟨t1, by omega, h1⟩
  obtain ⟨T1, hT1, hE⟩ := hempty _ T0 le_rfl le_rfl
  refine ⟨T1, by omega, fun t ht => ?_⟩
  have hEt : RecS (r.cfg t) = ∅ := Finset.subset_empty.mp (hE ▸ hmonoR' T1 t (by omega) ht)
  have hnr : ∀ q, ¬ ((r.cfg t).pc q).Rec := fun q hq => by
    have := mem_RecS.mpr hq; rw [hEt] at this; simp at this
  refine ⟨hnr, ?_⟩
  cases hh : (r.cfg t).holder with
  | none => rfl
  | some h =>
    exfalso
    rcases (hgood t (by omega)).holder_pos hh with hR | ⟨y, v, hpc⟩
    · exact hnr h (PC.rec_of_InR hR)
    · exact hnr h (by simp [hpc, PC.Rec, PC.isRec])

end Podc.RMESubLogBoth
